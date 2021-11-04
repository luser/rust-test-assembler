// Copyright 2015 Ted Mielczarek. See the COPYRIGHT
// file at the top-level directory of this distribution.

//! A set of types for building complex binary streams.
//!
//! For testing code that consumes binary data, it is necessary to
//! be able to generate test inputs consisting of various valid and
//! invalid permutations. The `Section` struct defined in this crate
//! allows for easily building a stream of bytes in any desired
//! endianness.
//!
//! This crate defines two useful structs: [`Section`] and
//! [`Label`]. A `Section` is simply a stream of bytes which can
//! be written to, and a `Label` is a placeholder for a value that can be
//! computed based on other values, but can be written to a `Section` without
//! knowing its value at that time.
//!
//! This crate is based on [Jim Blandy's fantastic C++ implementation][1] in Google Breakpad.
//!
//! [1]: https://chromium.googlesource.com/breakpad/breakpad/+/master/src/common/test_assembler.h
//!
//! # Examples
//!
//! `Section` provides many convenient methods for appending data of specific endianness and byte width. There are methods for appending 8, 16, 32, and 64-bit integers using the `Section`'s default  endianness, or explicitly using big or little-endian byte ordering. These methods all have shorthand names of the form:
//!
//! `[endianness][bits]`
//!
//! Where `endianness` is one of:
//! * `D`: The `Section`'s default endianness
//! * `L`: little-endian
//! * `B`: big-endian
//! And `bits` is any of 8, 16, 32, or 64 to write an integer from 1 to 8 bytes in length.
//!
//! So, for example, to write a little-endian 32-bit integer, call [`L32`](struct.Section.html#method.L32).
//!
//! The `Section` methods for appending data all consume and return the `Section`
//! so that they can be chained:
//!
//! ```
//! use test_assembler::Section;
//!
//! let mut section = Section::new();
//! section.D8(0xFF).L16(0xABCD).B32(0x12345678);
//! assert_eq!(section.get_contents().unwrap(),
//!            &[0xFF, 0xCD, 0xAB, 0x12, 0x34, 0x56, 0x78]);
//! ```
//!
//! `Label`s can be appended to a section as placeholders for values that
//! are not yet known using the same methods:
//!
//! ```
//! use test_assembler::*;
//!
//! let l = Label::new();
//! let mut s = Section::with_endian(Endian::Little);
//! s.D32(&l);
//! // Now assign a value to l.
//! l.set_const(0x12345678);
//! assert_eq!(s.get_contents().unwrap(),
//!            &[0x78, 0x56, 0x34, 0x12]);
//! ```
//!
//! `Label`s can also be set to the current length of the `Section` by calling
//! [`mark`][mark], which is useful for calculating an offset into the data:
//!
//! [mark]: struct.Section.html#method.mark
//!
//! ```
//! use test_assembler::*;
//!
//! let l = Label::new();
//! let mut s = Section::with_endian(Endian::Little);
//! let start = s.start();
//! s.append_repeated(0, 10)
//!     .mark(&l)
//!     .append_repeated(0, 10);
//! assert_eq!(&l - &start, 10);
//! ```

#![allow(non_snake_case)]
#![warn(rust_2018_idioms)]

#[cfg(doctest)]
doc_comment::doctest!("../README.md");

use std::{
    borrow::Borrow,
    cell::RefCell,
    fmt,
    io::{Cursor, Seek, SeekFrom, Write},
    ops::{Add, Deref, Sub},
    rc::Rc,
};

use byteorder::{BigEndian, LittleEndian, WriteBytesExt};

/// Possible byte orders
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Endian {
    Big,
    Little,
}

/// The default endianness for this system.
#[cfg(target_endian = "little")]
pub const DEFAULT_ENDIAN: Endian = Endian::Little;

/// The default endianness for this system.
#[cfg(target_endian = "big")]
pub const DEFAULT_ENDIAN: Endian = Endian::Big;

/// Potential values of a `Binding`.
enum BindingValue {
    /// A known constant value.
    Constant(u64),
    /// Equal to some other binding plus a constant.
    From(Rc<Binding>, i64),
    /// Free to take on any value.
    Unconstrained,
}

impl fmt::Debug for BindingValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            BindingValue::Constant(v) => write!(f, "Constant({})", v),
            BindingValue::From(ref b, v) => write!(f, "From({:?}, {})", b, v),
            BindingValue::Unconstrained => write!(f, "Unconstrained"),
        }
    }
}

/// A label's value, or if that is not yet known, how the value is related to other labels' values.
struct Binding {
    value: RefCell<BindingValue>,
}

impl fmt::Debug for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Binding {{ {:?} }}", self.value.borrow())
    }
}

/// These methods need to work with Rc<Binding>, so they go on a trait implemented for that type.
trait BindingOffset {
    /// Get the base `Binding` that this Binding references, as well
    /// as the sum of all offsets along the chain.
    fn get_base_and_offset(&self) -> (Rc<Binding>, i64);
    /// Return the offset between two bindings, if they are related.
    fn offset(&self, other: &Rc<Binding>) -> Option<i64>;
}

impl BindingOffset for Rc<Binding> {
    fn get_base_and_offset(&self) -> (Rc<Binding>, i64) {
        match *self.value.borrow().deref() {
            BindingValue::From(ref b, offset) => {
                let (base, base_offset) = b.get_base_and_offset();
                (base, base_offset + offset)
            }
            // If it's not From another binding, just return self.
            _ => (self.clone(), 0),
        }
    }

    fn offset(&self, other: &Rc<Binding>) -> Option<i64> {
        let (base, offset) = self.get_base_and_offset();
        let (other_base, other_offset) = other.get_base_and_offset();
        let base_ptr = base.deref() as *const Binding;
        let other_base_ptr = other_base.deref() as *const Binding;
        if base_ptr == other_base_ptr {
            // If the two bindings have the same base, then the offset is
            // the difference of their offsets.
            Some(offset - other_offset)
        } else {
            // Otherwise they are unrelated.
            None
        }
    }
}

impl Binding {
    /// Create a new Binding with an unconstrained value.
    pub fn unconstrained() -> Binding {
        Binding {
            value: RefCell::new(BindingValue::Unconstrained),
        }
    }
    /// Create a new Binding whose value is taken from another Binding.
    pub fn from(other: Rc<Binding>, offset: i64) -> Binding {
        Binding {
            value: RefCell::new(BindingValue::From(other, offset)),
        }
    }
    /// Create a new Binding with a constant value.
    pub fn constant(val: u64) -> Binding {
        Binding {
            value: RefCell::new(BindingValue::Constant(val)),
        }
    }

    /// Set this `Binding`s value to `val`.
    pub fn set_const(&self, val: u64) {
        let mut v = self.value.borrow_mut();
        *v = BindingValue::Constant(val);
    }
    /// Set this `Binding`s value equal to `other`.
    pub fn set(&self, other: Rc<Binding>) {
        let mut v = self.value.borrow_mut();
        let (base, offset) = other.get_base_and_offset();
        *v = BindingValue::From(base, offset);
    }
    /// Get the constant value of the `Binding`, if known.
    pub fn value(&self) -> Option<u64> {
        match *self.value.borrow() {
            // If this Binding is a constant, this is easy.
            BindingValue::Constant(c) => Some(c),
            // If this Binding is based on another Binding, ask it for its
            // value.
            BindingValue::From(ref base, addend) => base.value().map(|v| v + addend as u64),
            // If this Binding is unconstrained then its value is not known.
            _ => None,
        }
    }
}

#[doc(hidden)]
pub struct RealLabel {
    binding: Rc<Binding>,
}

impl fmt::Debug for RealLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.binding)
    }
}

/// Methods for creating a `Label` (or a `RealLabel`, but don't do that).
pub trait LabelMaker {
    /// Create an undefined label.
    fn new() -> Self;
    /// Create a label with a constant value `val`.
    fn from_const(val: u64) -> Self;
    /// Create a label whose value is equal to `other`.
    fn from_label(other: &Self) -> Self;
    /// Create a label whose value is equal to `other` plus `offset`.
    fn from_label_offset(other: &Self, offset: i64) -> Self;
}

impl RealLabel {
    /// Get the constant value of the `RealLabel`, if known.
    pub fn value(&self) -> Option<u64> {
        self.binding.value()
    }
    /// Get the relative offset from another label, if possible.
    pub fn offset(&self, other: &RealLabel) -> Option<i64> {
        // Let the Binding calculate the offset.
        self.binding.offset(&other.binding)
    }
    /// Set this `RealLabel`s value to `val`.
    pub fn set_const(&self, val: u64) {
        self.binding.set_const(val);
    }
    /// Set this `RealLabel`s value equal to `other`.
    pub fn set(&self, other: &RealLabel) {
        //TODO: could use some sanity checks here?
        self.binding.set(other.binding.clone())
    }
}

impl LabelMaker for RealLabel {
    fn new() -> RealLabel {
        RealLabel {
            binding: Rc::new(Binding::unconstrained()),
        }
    }
    fn from_const(val: u64) -> RealLabel {
        RealLabel {
            binding: Rc::new(Binding::constant(val)),
        }
    }
    fn from_label(other: &RealLabel) -> RealLabel {
        RealLabel {
            binding: other.binding.clone(),
        }
    }
    fn from_label_offset(other: &RealLabel, offset: i64) -> RealLabel {
        RealLabel {
            binding: Rc::new(Binding::from(other.binding.clone(), offset)),
        }
    }
}

/// A `Label` represents a value not yet known that is stored in a `Section`.
///
/// As long as all the labels a section refers to are defined
/// by the time its contents are retrieved as bytes, undefined
/// labels can be used freely in that section's construction.
/// A label can be in one of three states:
///
/// * undefined,
/// * defined as the sum of some other label and a constant, or
/// * a constant.
///
/// A label's value never changes, but it can accumulate constraints.
/// Adding labels and integers is permitted, and yields a label.
/// Subtracting a constant from a label is permitted, and also yields a
/// label. Subtracting two labels that have some relationship to each
/// other is permitted, and yields a constant.
///
/// A common usage of `Label` is to use [`Section::mark`] to make a `Label`
/// contain an offset into the `Section` without having to hard-code it.
/// The `Section` methods for inserting fixed-width integer values (such as
/// [`Section::L32`]) all accept `&Label` for the purpose of writing a value
/// that is not yet available.
///
/// # Examples
///
/// `Label`s can be set to point to other `Label`s, potentially with an offset.
///
/// ```
/// use test_assembler::*;
///
/// let l1 = Label::new();
/// // l2 is l1's value (which is currently undefined) + 10
/// let l2 = &l1 + 10;
/// // Now give l1 a value.
/// l1.set_const(1);
/// // l2's value is derived from l1.
/// assert_eq!(l2.value().unwrap(), 11);
/// ```
#[derive(Clone)]
pub struct Label(pub Rc<RealLabel>);

impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Label {{ {:?} }}", self.0)
    }
}

impl Deref for Label {
    type Target = RealLabel;

    fn deref(&self) -> &RealLabel {
        let &Label(ref inner) = self;
        inner.deref()
    }
}

impl LabelMaker for Label {
    fn new() -> Label {
        Label(Rc::new(RealLabel::new()))
    }
    fn from_const(val: u64) -> Label {
        Label(Rc::new(RealLabel::from_const(val)))
    }
    fn from_label(other: &Label) -> Label {
        let &Label(ref inner) = other;
        Label(Rc::new(RealLabel::from_label(inner.borrow())))
    }
    fn from_label_offset(other: &Label, offset: i64) -> Label {
        let &Label(ref inner) = other;
        Label(Rc::new(RealLabel::from_label_offset(
            inner.borrow(),
            offset,
        )))
    }
}

/// Add a constant to a `Label`, producing a new `Label`.
///
/// The new `Label` references the existing `Label`.
impl<'a> Add<i64> for &'a Label {
    type Output = Label;

    fn add(self, rhs: i64) -> Label {
        Label::from_label_offset(self, rhs)
    }
}

/// Subtract a constant from a `Label`, producing a new `Label`.
///
/// The new `Label` references the existing `Label`.
impl<'a> Sub<i64> for &'a Label {
    type Output = Label;

    fn sub(self, rhs: i64) -> Label {
        Label::from_label_offset(self, -rhs)
    }
}

/// Subtract a `Label` from another `Label`, returning an `i64`.
///
/// If the labels are unrelated this will panic.
impl<'a> Sub<&'a Label> for &'a Label {
    type Output = i64;

    fn sub(self, rhs: &'a Label) -> i64 {
        self.offset(rhs).unwrap()
    }
}

/// A marker trait for number types.
pub trait Num {}

impl Num for u8 {}
impl Num for u16 {}
impl Num for u32 {}
impl Num for u64 {}

/// An enum to hold `Label`s or `Num`s.
pub enum LabelOrNum<T: Num> {
    Label(Label),
    Num(T),
}

/// A trait to allow passing numbers or Labels.
pub trait ToLabelOrNum<'a, T: Num> {
    fn to_labelornum(self) -> LabelOrNum<T>;
}

impl<'a, T: Num> ToLabelOrNum<'a, T> for Label {
    fn to_labelornum(self) -> LabelOrNum<T> {
        LabelOrNum::Label(self)
    }
}

impl<'a, T: Num> ToLabelOrNum<'a, T> for &'a Label {
    fn to_labelornum(self) -> LabelOrNum<T> {
        LabelOrNum::Label(self.clone())
    }
}

impl<'a, T: Num> ToLabelOrNum<'a, T> for T {
    fn to_labelornum(self) -> LabelOrNum<T> {
        LabelOrNum::Num(self)
    }
}

/// A reference to a `Label` that has been appended to a `Section`.
#[derive(Clone)]
struct Reference {
    /// The `Label` being referenced.
    label: Label,
    /// The offset of the reference within the `Section`.
    offset: u64,
    /// The endianness with which the `Label` should be stored.
    endian: Endian,
    /// The size with which the `Label` should be stored.
    size: usize,
}

/// A section is a sequence of bytes, constructed by appending bytes to the end.
///
/// Sections have a convenient and flexible set of member
/// functions for appending data in various formats: big-endian and
/// little-endian signed and unsigned values of different sizes, and
/// raw blocks of bytes.
///
/// There are methods for appending each of `u8`, `u16`, `u32`, and `u64`
/// in each of big, little, or the `Section`'s default endianness.
/// The method names are {D,L,B}{8,16,32,64} for each variant, so
/// [`D16`][D16] writes a `u16` in the `Section`'s default endianness, and
/// [`L64`][L64] writes a `u64` in little-endian byte order.
///
/// Each of these methods also accepts a [`Label`][Label] to write
/// non-constant values.
///
/// See [the module-level documentation][module] for examples.
///
/// [module]: index.html
/// [D16]: #method.D16
/// [L64]: #method.L64
/// [Label]: struct.Label.html
pub struct Section {
    /// The current endianness of the writer.
    ///
    /// This sets the behavior of the D<N> appending functions.
    pub endian: Endian,
    /// The contents of the section.
    contents: Cursor<Vec<u8>>,
    /// References to `Label`s that were added to this `Section`.
    references: Vec<Reference>,
    /// A label representing the start of this `Section`.
    start: Label,
    /// A label representing the final size of this `Section`.
    final_size: Label,
}

impl Section {
    /// Construct a `Section` with platform-default endianness.
    #[inline]
    pub fn new() -> Self {
        Self::with_endian(DEFAULT_ENDIAN)
    }

    /// Construct a `Section` with `endian` endianness.
    #[inline]
    pub fn with_endian(endian: Endian) -> Self {
        Self {
            endian,
            contents: Cursor::new(vec![]),
            references: vec![],
            start: Label::new(),
            final_size: Label::new(),
        }
    }

    /// Constructs a `Section` via a user supplied for simpler one-liners
    pub fn inline(endian: Option<Endian>, func: impl FnOnce(&mut Self) -> &mut Self) -> Self {
        let mut this = Self::with_endian(endian.unwrap_or(DEFAULT_ENDIAN));

        func(&mut this);

        this
    }

    /// Return the current size of the section.
    #[inline]
    pub fn size(&self) -> u64 {
        self.contents.get_ref().len() as u64
    }

    /// Return a `Label` that will resolve to the final size of the section.
    ///
    /// This label is undefined until `get_contents` is called.
    #[inline]
    pub fn final_size(&self) -> Label {
        self.final_size.clone()
    }

    /// Get the contents of this section as a slice of bytes.
    ///
    /// Consumes the section. If there were still undefined labels,
    /// return `None`.
    pub fn get_contents(self) -> Option<Vec<u8>> {
        // Patch all labels into the section's contents.
        let mut section = self;
        section.final_size.set_const(section.size());

        for rf in section.references.clone() {
            let val = rf.label.value()?;
            section.store_label_value(val, rf.offset, rf.endian, rf.size);
        }

        Some(section.contents.into_inner())
    }

    /// Return a label representing the start of the section.
    ///
    /// It is up to the user whether this label represents the section's
    /// position in an object file, the section's address in memory, or
    /// what have you; some applications may need both, in which case
    /// this simple-minded interface won't be enough. This class only
    /// provides a single start label, for use with the `here` and `mark`
    /// methods.
    #[inline]
    pub fn start(&self) -> Label {
        self.start.clone()
    }

    /// A label representing the point at which the next appended item will appear in the section, relative to `start`.
    #[inline]
    pub fn here(&self) -> Label {
        &self.start + self.size() as i64
    }

    /// Set the value of `start` to `value`.
    #[inline]
    pub fn set_start_const(&mut self, value: u64) -> &mut Self {
        self.start.set_const(value);
        self
    }

    /// Set `label` to [`here`](#method.here), and return this section.
    #[inline]
    pub fn mark(&mut self, label: &Label) -> &mut Self {
        label.set(&self.here());
        self
    }

    /// Append `data` to the end of this section, and return this section.
    #[inline]
    pub fn append_bytes(&mut self, data: &[u8]) -> &mut Self {
        self.contents.write_all(data).unwrap();
        self
    }

    /// Append `section`'s contents to the end of this section.
    ///
    /// Any `Label`s that were appended to `section` will not be
    /// resolved until this section is finalized.
    /// Return this section.
    pub fn append_section(&mut self, section: impl Into<Self>) -> &mut Self {
        let Section {
            contents,
            references,
            final_size,
            ..
        } = section.into();
        final_size.set_const(contents.get_ref().len() as u64);
        let current = self.size();
        self.contents.write_all(&contents.into_inner()).unwrap();
        self.references.extend(references.into_iter().map(|mut r| {
            r.offset += current;
            r
        }));
        self
    }

    /// Append `count` copies of `byte` to the end of this section.
    ///
    /// Return this section.
    #[inline]
    pub fn append_repeated(&mut self, byte: u8, count: usize) -> &mut Self {
        for _ in 0..count {
            self.contents.write_u8(byte).unwrap();
        }
        self
    }

    /// Jump to the next location aligned on an `alignment`-byte boundary, relative to the start of the section.
    ///
    /// Fill the gap with zeroes. `alignment` must be a power of two.
    /// Return this section.
    #[inline]
    pub fn align(&mut self, alignment: u64) -> &mut Self {
        // `alignment` must be a power of two.
        assert!(((alignment - 1) & alignment) == 0);
        let new_size = (self.size() + alignment - 1) & !(alignment - 1);
        let add = new_size - self.size();
        self.append_repeated(0, add as usize)
    }

    fn store_label_value(
        &mut self,
        val: u64,
        offset: u64,
        endian: Endian,
        size: usize,
    ) -> &mut Self {
        let current = self.size();
        if offset != current {
            self.contents.seek(SeekFrom::Start(offset)).unwrap();
        }
        match endian {
            Endian::Little => match size {
                1 => self.L8(val as u8),
                2 => self.L16(val as u16),
                4 => self.L32(val as u32),
                8 => self.L64(val),
                _ => unreachable!("Unhandled label size!"),
            },
            Endian::Big => match size {
                1 => self.B8(val as u8),
                2 => self.B16(val as u16),
                4 => self.B32(val as u32),
                8 => self.B64(val),
                _ => unreachable!("Unhandled label size!"),
            },
        }
    }

    /// Append `label` to the Section with `endian` endianness, taking `size` bytes.
    ///
    /// Panics if `size` is not an intrinsic integer size: 1, 2, 4, 8 bytes.
    fn append_label(&mut self, label: &Label, endian: Endian, size: usize) -> &mut Self {
        let current = self.size();
        // For labels with a known value, don't bother with a reference.
        if let Some(val) = label.value() {
            self.store_label_value(val, current, endian, size)
        } else {
            // label isn't yet known, need to store a reference.
            self.references.push(Reference {
                label: label.clone(),
                offset: current,
                endian,
                size,
            });
            // Reserve space for the label.
            self.append_repeated(0, size)
        }
    }

    /// Append `byte` with the Section's default endianness.
    ///
    /// `byte` may be a `Label` or a `u8`.
    /// Return this section.
    pub fn D8<'a, T: ToLabelOrNum<'a, u8>>(&mut self, byte: T) -> &mut Self {
        let endian = self.endian;
        match byte.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u8(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, endian, 1),
        }
    }
    /// Append `byte` as little-endian (identical to `D8`).
    ///
    /// Return this section.
    pub fn L8<'a, T: ToLabelOrNum<'a, u8>>(&mut self, byte: T) -> &mut Self {
        self.D8(byte)
    }
    /// Append `byte` as big-endian (identical to `D8`).
    ///
    /// Return this section.
    pub fn B8<'a, T: ToLabelOrNum<'a, u8>>(&mut self, byte: T) -> &mut Self {
        self.D8(byte)
    }

    /// Append `word` with the Section's default endianness.
    ///
    /// `word` may be a `Label` or a `u16`.
    /// Return this section.
    pub fn D16<'a, T: ToLabelOrNum<'a, u16>>(&mut self, word: T) -> &mut Self {
        match self.endian {
            Endian::Little => self.L16(word),
            Endian::Big => self.B16(word),
        }
    }
    /// Append `word` as little-endian.
    ///
    /// `word` may be a `Label` or a `u16`.
    /// Return this section.
    pub fn L16<'a, T: ToLabelOrNum<'a, u16>>(&mut self, word: T) -> &mut Self {
        match word.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u16::<LittleEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Little, 2),
        }
    }
    /// Append `word` as big-endian.
    ///
    /// `word` may be a `Label` or a `u16`.
    /// Return this section.
    pub fn B16<'a, T: ToLabelOrNum<'a, u16>>(&mut self, word: T) -> &mut Self {
        match word.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u16::<BigEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Big, 2),
        }
    }

    /// Append `dword` with the Section's default endianness.
    ///
    /// `dword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn D32<'a, T: ToLabelOrNum<'a, u32>>(&mut self, dword: T) -> &mut Self {
        match self.endian {
            Endian::Little => self.L32(dword),
            Endian::Big => self.B32(dword),
        }
    }
    /// Append `dword` as little-endian.
    ///
    /// `dword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn L32<'a, T: ToLabelOrNum<'a, u32>>(&mut self, dword: T) -> &mut Self {
        match dword.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u32::<LittleEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Little, 4),
        }
    }
    /// Append `dword` as big-endian.
    ///
    /// `dword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn B32<'a, T: ToLabelOrNum<'a, u32>>(&mut self, dword: T) -> &mut Self {
        match dword.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u32::<BigEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Big, 4),
        }
    }

    /// Append `qword` with the Section's default endianness.
    ///
    /// `qword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn D64<'a, T: ToLabelOrNum<'a, u64>>(&mut self, qword: T) -> &mut Self {
        match self.endian {
            Endian::Little => self.L64(qword),
            Endian::Big => self.B64(qword),
        }
    }
    /// Append `qword` as little-endian.
    ///
    /// `qword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn L64<'a, T: ToLabelOrNum<'a, u64>>(&mut self, qword: T) -> &mut Self {
        match qword.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u64::<LittleEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Little, 8),
        }
    }
    /// Append `qword` as big-endian.
    ///
    /// `qword` may be a `Label` or a `u32`.
    /// Return this section.
    pub fn B64<'a, T: ToLabelOrNum<'a, u64>>(&mut self, qword: T) -> &mut Self {
        match qword.to_labelornum() {
            LabelOrNum::Num(n) => {
                self.contents.write_u64::<BigEndian>(n).unwrap();
                self
            }
            LabelOrNum::Label(l) => self.append_label(&l, Endian::Big, 8),
        }
    }
}

impl Default for Section {
    fn default() -> Self {
        Section::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn binding_offset() {
        let b_u = Rc::new(Binding::unconstrained());
        let b_c = Rc::new(Binding::constant(1));
        let b_f1 = Rc::new(Binding::from(b_u.clone(), 0));
        // b_f1 is equal to b_u, so the offset should be zero.
        assert_eq!(b_f1.offset(&b_u).unwrap(), 0);
        // b_f1 and b_c are unrelated
        assert!(b_f1.offset(&b_c).is_none());
        // as are b_u and b_c.
        assert!(b_u.offset(&b_c).is_none());
        assert!(b_c.offset(&b_u).is_none());

        let b_f2 = Rc::new(Binding::from(b_c.clone(), 10));
        // b_f2 is a non-zero offset from b_c.
        assert_eq!(b_f2.offset(&b_c).unwrap(), 10);
        // We need to go deeper.
        let b_f3 = Rc::new(Binding::from(b_f1, 10));
        assert_eq!(b_f3.offset(&b_u).unwrap(), 10);
        let b_f4 = Rc::new(Binding::from(b_f3.clone(), 10));
        assert_eq!(b_f4.offset(&b_u).unwrap(), 20);
        // Make another chain of bindings so we can test that the leaves of
        // both chains compare properly.
        // <INCEPTION HORN>
        let b_f5 = Rc::new(Binding::from(b_u.clone(), 10));
        let b_f6 = Rc::new(Binding::from(b_f5.clone(), 10));
        assert_eq!(b_f6.offset(&b_f5).unwrap(), 10);
        assert_eq!(b_f6.offset(&b_u).unwrap(), 20);
        // Now for the kicker, b_f6 and b_f4 should be the same value, since
        // they're both b_u + 20.
        assert_eq!(b_f6.offset(&b_f4).unwrap(), 0);
        // and some additional checks.
        assert_eq!(b_f6.offset(&b_f3).unwrap(), 10);
        assert_eq!(b_f3.offset(&b_f6).unwrap(), -10);
    }

    #[test]
    fn binding_value() {
        let b_u = Rc::new(Binding::unconstrained());
        let b_c = Rc::new(Binding::constant(1));
        let b_f1 = Rc::new(Binding::from(b_u.clone(), 0));
        assert!(b_u.value().is_none());
        assert_eq!(b_c.value().unwrap(), 1);
        assert!(b_f1.value().is_none());

        let b_f2 = Rc::new(Binding::from(b_c, 10));
        assert_eq!(b_f2.value().unwrap(), 11);
        // We need to go deeper.
        let b_f3 = Rc::new(Binding::from(b_f1, 10));
        assert!(b_f3.value().is_none());
        let b_f4 = Rc::new(Binding::from(b_f3, 10));
        assert!(b_f4.value().is_none());

        let b_f5 = Rc::new(Binding::from(b_f2, 10));
        assert_eq!(b_f5.value().unwrap(), 21);
    }

    #[test]
    fn label_unconstrained() {
        let l = Label::new();
        assert!(l.value().is_none());
    }

    #[test]
    fn label_const() {
        let l = Label::from_const(10);
        assert_eq!(l.value().unwrap(), 10);
    }

    #[test]
    fn label_label() {
        let l1 = Label::new();
        let l2 = Label::from_label(&l1);
        assert!(l2.value().is_none());
        // The offset should work both ways.
        assert_eq!(l2.offset(&l1).unwrap(), 0);
        assert_eq!(l1.offset(&l2).unwrap(), 0);
    }

    #[test]
    fn label_label_offset() {
        let l1 = Label::new();
        let l2 = Label::from_label_offset(&l1, 10);
        assert!(l2.value().is_none());
        assert_eq!(l2.offset(&l1).unwrap(), 10);
        assert_eq!(l1.offset(&l2).unwrap(), -10);

        let l3 = Label::from_label_offset(&l2, 10);
        assert_eq!(l3.offset(&l2).unwrap(), 10);
        assert_eq!(l2.offset(&l3).unwrap(), -10);
        assert_eq!(l3.offset(&l1).unwrap(), 20);
        assert_eq!(l1.offset(&l3).unwrap(), -20);

        let l4 = Label::from_label_offset(&l3, 10);
        assert_eq!(l4.offset(&l1).unwrap(), 30);

        // Check that chains of label offsets work properly.
        let l5 = Label::from_label_offset(&l1, 10);
        // l5 and l2 are both l1 + 10.
        assert_eq!(l5.offset(&l2).unwrap(), 0);
        assert_eq!(l5.offset(&l3).unwrap(), -10);
        assert_eq!(l3.offset(&l5).unwrap(), 10);
    }

    #[test]
    fn label_offset_unrelated() {
        let l1 = Label::new();
        let l2 = Label::new();
        assert!(l2.offset(&l1).is_none());
        assert!(l1.offset(&l2).is_none());
    }

    #[test]
    fn label_add() {
        let l1 = Label::new();
        let l2 = &l1 + 10;
        assert_eq!(l2.offset(&l1).unwrap(), 10);
    }

    #[test]
    fn label_sub() {
        let l1 = Label::new();
        let l2 = &l1 - 10;
        assert_eq!(l2.offset(&l1).unwrap(), -10);
    }

    #[test]
    fn label_sub_label() {
        let l1 = Label::new();
        let l2 = &l1 + 10;
        assert_eq!(&l2 - &l1, 10);
    }

    #[test]
    fn label_set_const() {
        let l = Label::new();
        let val = 0x12345678;
        l.set_const(val);
        assert_eq!(l.value().unwrap(), val);
    }

    #[test]
    fn label_set() {
        let val = 0x12345678;
        let l1 = Label::from_const(val);
        let l2 = Label::new();
        l2.set(&l1);
        assert_eq!(l2.value().unwrap(), val);
        // Check that setting the first value's label *after* the call to set works.
        let l3 = Label::new();
        let l4 = Label::new();
        l4.set(&l3);
        l3.set_const(val);
        assert_eq!(l4.value().unwrap(), val);
    }

    #[test]
    fn section_construction() {
        let s = Section::new();
        assert_eq!(s.endian, DEFAULT_ENDIAN);

        let s2 = Section::with_endian(Endian::Little);
        assert_eq!(s2.endian, Endian::Little);
    }

    #[test]
    fn section_append_bytes() {
        let b1 = [0, 1, 2, 3, 4];
        let b2 = [0xf, 0xe, 0xd, 0xc, 0xb];
        assert_eq!(
            Section::inline(None, |s| s.append_bytes(&b1).append_bytes(&b2))
                .get_contents()
                .unwrap(),
            &[0, 1, 2, 3, 4, 0xf, 0xe, 0xd, 0xc, 0xb]
        );
    }

    #[test]
    fn section_final_size() {
        let mut s = Section::new();
        let size = s.final_size();
        s.append_repeated(0, 20);
        s.get_contents().unwrap();
        assert_eq!(size.value().unwrap(), 20);
    }

    #[test]
    fn section_append_section_simple() {
        assert_eq!(
            Section::inline(None, |s| s
                .D8(0xab)
                .append_section(Section::inline(None, |s| s.D8(0xcd)))
                .D8(0xef))
            .get_contents()
            .unwrap(),
            &[0xab, 0xcd, 0xef]
        );
    }

    #[test]
    fn section_append_section_labels() {
        let mut s = Section::new();
        let l1 = Label::from_const(0x12);
        let l2 = Label::new();
        s.D8(0xab);
        {
            s.append_section(Section::inline(None, |s| s.D8(0xcd).D8(&l1).D8(&l2)));
        }
        s.D8(0xef);
        l2.set_const(0x34);
        assert_eq!(s.get_contents().unwrap(), &[0xab, 0xcd, 0x12, 0x34, 0xef]);
    }

    #[test]
    fn section_append_section_final_size() {
        let sub = Section::inline(None, |s| s.D8(0xcd));
        assert_eq!(
            Section::inline(None, |s| {
                let final_size = s.final_size();
                s.D8(0xab).D8(&final_size).append_section(sub).D8(0xef)
            })
            .get_contents()
            .unwrap(),
            &[0xab, 4, 0xcd, 0xef]
        );
    }

    #[test]
    fn section_append_repeated() {
        assert_eq!(
            Section::inline(None, |s| s.append_repeated(0xff, 5))
                .get_contents()
                .unwrap(),
            &[0xff, 0xff, 0xff, 0xff, 0xff]
        );
    }

    #[test]
    fn section_align() {
        assert_eq!(
            Section::inline(None, |s| s.D8(1).align(8).D8(1))
                .get_contents()
                .unwrap(),
            &[1, 0, 0, 0, 0, 0, 0, 0, 1]
        );
    }

    #[test]
    fn section_test_8() {
        assert_eq!(
            Section::inline(None, |s| s.D8(0x12).L8(0x12).B8(0x12))
                .get_contents()
                .unwrap(),
            &[0x12, 0x12, 0x12]
        );
    }

    #[test]
    fn section_test_16() {
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s
                .D16(0xABCD)
                .L16(0xABCD)
                .B16(0xABCD))
            .get_contents()
            .unwrap(),
            &[0xCD, 0xAB, 0xCD, 0xAB, 0xAB, 0xCD]
        );
    }

    #[test]
    fn section_test_32() {
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s
                .D32(0xABCD1234)
                .L32(0xABCD1234)
                .B32(0xABCD1234))
            .get_contents()
            .unwrap(),
            &[0x34, 0x12, 0xCD, 0xAB, 0x34, 0x12, 0xCD, 0xAB, 0xAB, 0xCD, 0x12, 0x34]
        );
    }

    #[test]
    fn section_test_64() {
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s
                .D64(0x12345678ABCDEFFF)
                .L64(0x12345678ABCDEFFF)
                .B64(0x12345678ABCDEFFF))
            .get_contents()
            .unwrap(),
            &[
                0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56, 0x34, 0x12, 0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56,
                0x34, 0x12, 0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF, 0xFF
            ]
        );
    }

    #[test]
    fn section_d8l_const_label() {
        let l = Label::from_const(10);
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s.D8(&l).L8(&l).B8(&l))
                .get_contents()
                .unwrap(),
            &[10, 10, 10]
        );
    }

    #[test]
    fn section_d16l_const_label() {
        let l = Label::from_const(0xABCD);
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s.D16(&l).L16(&l).B16(&l))
                .get_contents()
                .unwrap(),
            &[0xCD, 0xAB, 0xCD, 0xAB, 0xAB, 0xCD]
        );
    }

    #[test]
    fn section_d32l_const_label() {
        let l = Label::from_const(0xABCD1234);
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s.D32(&l).L32(&l).B32(&l))
                .get_contents()
                .unwrap(),
            &[0x34, 0x12, 0xCD, 0xAB, 0x34, 0x12, 0xCD, 0xAB, 0xAB, 0xCD, 0x12, 0x34]
        );
    }

    #[test]
    fn section_d64l_const_label() {
        let l = Label::from_const(0xABCD12345678F00D);
        assert_eq!(
            Section::inline(Some(Endian::Little), |s| s.D64(&l).L64(&l).B64(&l))
                .get_contents()
                .unwrap(),
            &[
                0x0D, 0xF0, 0x78, 0x56, 0x34, 0x12, 0xCD, 0xAB, 0x0D, 0xF0, 0x78, 0x56, 0x34, 0x12,
                0xCD, 0xAB, 0xAB, 0xCD, 0x12, 0x34, 0x56, 0x78, 0xF0, 0x0D
            ]
        );
    }

    #[test]
    fn section_get_contents_label_no_value() {
        // Trying to get_contents on a Section when a Label that was added
        // has no value should return None.
        let l = Label::new();
        assert!(Section::inline(Some(Endian::Little), |s| s.D8(&l))
            .get_contents()
            .is_none());
    }

    #[test]
    fn section_label_assign_late() {
        let l = Label::new();
        let s = Section::inline(Some(Endian::Little), |s| s.D8(&l).L8(&l).B8(&l));
        // Now assign a value to l.
        l.set_const(10);
        assert_eq!(s.get_contents().unwrap(), &[10, 10, 10]);
    }

    #[test]
    fn section_start_here() {
        let mut s = Section::with_endian(Endian::Little);
        s.append_repeated(0, 10);
        let start = s.start();
        let mut here = s.here();
        assert_eq!(here.offset(&start).unwrap(), 10);
        s.append_repeated(0, 10);
        here = s.here();
        assert_eq!(here.offset(&start).unwrap(), 20);
    }

    #[test]
    fn section_start_mark() {
        let mut s = Section::with_endian(Endian::Little);
        let start = s.start();
        let marked = Label::new();
        s.append_repeated(0, 10)
            .mark(&marked)
            .append_repeated(0, 10);
        assert_eq!(marked.offset(&start).unwrap(), 10);
    }

    #[test]
    fn section_additional_methods_trait() {
        trait ExtraSection {
            fn add_a_thing(&mut self) -> &mut Self;
        }

        impl ExtraSection for Section {
            fn add_a_thing(&mut self) -> &mut Self {
                self.B8(0x12).B16(0x3456).B32(0x7890abcd)
            }
        }

        assert_eq!(
            Section::inline(None, |s| s.D8(0).add_a_thing().D8(1))
                .get_contents()
                .unwrap(),
            &[0, 0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 1]
        );
    }

    #[test]
    fn test_simple_labels() {
        let start = Label::new();
        let end = Label::new();

        Section::inline(None, |s| s.mark(&start).mark(&end));

        assert_eq!(start.offset(&end), Some(0));
    }

    #[test]
    fn test_set_start_const() {
        let l = Label::new();
        Section::inline(None, |s| {
            s.set_start_const(0).append_repeated(0, 10).mark(&l)
        })
        .get_contents()
        .unwrap();
        assert_eq!(l.value().unwrap(), 10);
    }

    #[test]
    fn section_bigendian_defaults() {
        assert_eq!(
            Section::inline(Some(Endian::Big), |s| s
                .D8(0x12)
                .D16(0x1234)
                .D32(0x12345678)
                .D64(0x12345678ABCDEFFF))
            .get_contents()
            .unwrap(),
            &[
                0x12, 0x12, 0x34, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF,
                0xFF
            ]
        );
    }
}

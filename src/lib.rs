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
//! Based on [Jim Blandy's fantastic C++ implementation][1] in Google Breakpad.
//! [1]: https://chromium.googlesource.com/breakpad/breakpad/+/master/src/common/test_assembler.h
//! # Examples
//!
//! The methods for writing data all consume and return the `Section`
//! so that they can be chained:
//!
//! ```
//! use test_assembler::Section;
//!
//! let mut section = Section::new();
//! assert_eq!(section.D8(0xFF).L16(0xABCD).B32(0x12345678)
//!             .get_contents().unwrap(),
//!            &[0xFF, 0xCD, 0xAB, 0x12, 0x34, 0x56, 0x78]);
//! ```
//!
//! `Label`s can be appended to a section as placeholders for values that
//! are not yet known, using the same methods but with an L suffix:
//!
//! ```
//! use test_assembler::*;
//!
//! let l = Label::new();
//! let mut s = Section::with_endian(Endian::Little);
//! s = s.D32L(&l);
//! // Now assign a value to l.
//! l.set_const(0x12345678);
//! assert_eq!(s.get_contents().unwrap(),
//!            &[0x78, 0x56, 0x34, 0x12]);
//! ```

#![allow(non_snake_case)]

extern crate byteorder;

use std::borrow::Borrow;
use std::cell::RefCell;
use std::io::Cursor;
use std::io::Seek;
use std::io::SeekFrom;
use std::io::Write;
use std::ops::{Add,Deref,Sub};
use std::rc::Rc;

use byteorder::{ByteOrder,BigEndian,LittleEndian,WriteBytesExt};

/// Possible byte orders
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Endian {
    Big,
    Little,
}

/// The default endianness for this system.
#[cfg(target_endian = "little")]
pub const DEFAULT_ENDIAN : Endian = Endian::Little;

/// The default endianness for this system.
#[cfg(target_endian = "big")]
pub const DEFAULT_ENDIAN : Endian = Endian::Big;

/// Potential values of a `Binding`.
enum BindingValue {
    /// A known constant value.
    Constant(u64),
    /// Equal to some other binding plus a constant.
    From(Rc<Binding>, i64),
    /// Free to take on any value.
    Unconstrained,
}

/// A label's value, or if that is not yet known, how the value is related to other labels' values.
struct Binding {
    value : RefCell<BindingValue>,
}

impl Binding {
    /// Create a new Binding with an unconstrained value.
    pub fn unconstrained() -> Binding {
        Binding { value: RefCell::new(BindingValue::Unconstrained) }
    }
    /// Create a new Binding whose value is taken from another Binding.
    pub fn from(other : Rc<Binding>, offset : i64) -> Binding {
        Binding { value: RefCell::new(BindingValue::From(other, offset)) }
    }
    /// Create a new Binding with a constant value.
    pub fn constant(val : u64) -> Binding {
        Binding { value: RefCell::new(BindingValue::Constant(val)) }
    }
    /// Set this `Binding`s value to `val`.
    pub fn set_const(&self, val : u64) {
        let mut v = self.value.borrow_mut();
        *v = BindingValue::Constant(val);
    }
    /// Set this `Binding`s value equal to `other`.
    pub fn set(&self, other : Rc<Binding>) {
        let mut v = self.value.borrow_mut();
        *v = BindingValue::From(other, 0);
    }
    /// Get the constant value of the `Binding`, if known.
    pub fn value(&self) -> Option<u64> {
        match *self.value.borrow() {
            // If this Binding is a constant, this is easy.
            BindingValue::Constant(c) => Some(c),
            // If this Binding is based on another Binding, ask it for its
            // value.
            BindingValue::From(ref base, addend) =>
                base.value().and_then(|v| Some(v + addend as u64)),
            // If this Binding is unconstrained then its value is not known.
            _ => None,
        }
    }
    /// Return the offset between two bindings, if they are related.
    pub fn offset(&self, other : &Binding) -> Option<i64> {
        let other_ptr = other as *const Binding;
        let self_ptr = self as *const Binding;
        // If self is other, then the offset is zero.
        if self_ptr == other_ptr {
            return Some(0);
        }
        // If this binding isn't specified relative to another label then
        // the answer is None.
        if let BindingValue::From(ref b, offset) = *self.value.borrow() {
            // Get the answer from `b`, and add this binding's offfset.
            b.offset(other).and_then(|val| Some(val + offset))
        } else {
            None
        }
    }
}

/// The inner workings of `Label`. Don't instanitate this, instantiate `Label`.
pub struct RealLabel {
    binding : Rc<Binding>,
}

/// Methods for creating a `Label` (or a `RealLabel`, but don't do that).
pub trait LabelMaker {
    /// Create an undefined label.
    fn new() -> Self;
    /// Create a label with a constant value `val`.
    fn from_const(val : u64) -> Self;
    /// Create a label whose value is equal to `other`.
    fn from_label(other : &Self) -> Self;
    /// Create a label whose value is equal to `other` plus `offset`.
    fn from_label_offset(other : &Self, offset : i64) -> Self;
}

impl RealLabel {
    /// Get the constant value of the `RealLabel`, if known.
    pub fn value(&self) -> Option<u64> {
        self.binding.value()
    }
    /// Get the relative offset from another label, if possible.
    pub fn offset(&self, other : &RealLabel) -> Option<i64> {
        // Let the Binding calculate the offset, but try both directions.
        self.binding.offset(&other.binding)
            // Going the other direction the offsets are negative.
            .or(other.binding.offset(&self.binding).and_then(|v| Some(-v)))
    }
    /// Set this `RealLabel`s value to `val`.
    pub fn set_const(&self, val : u64) {
        self.binding.set_const(val);
    }
    /// Set this `RealLabel`s value equal to `other`.
    pub fn set(&self, other : &RealLabel) {
        //TODO: could use some sanity checks here?
        self.binding.set(other.binding.clone())
    }
}

impl LabelMaker for RealLabel {
    fn new() -> RealLabel {
        RealLabel { binding: Rc::new(Binding::unconstrained()) }
    }
    fn from_const(val : u64) -> RealLabel {
        RealLabel { binding: Rc::new(Binding::constant(val)) }
    }
    fn from_label(other : &RealLabel) -> RealLabel {
        RealLabel { binding: other.binding.clone() }
    }
    fn from_label_offset(other : &RealLabel, offset : i64) -> RealLabel {
        RealLabel { binding: Rc::new(Binding::from(other.binding.clone(), offset)) }
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

impl Deref for Label {
    type Target = RealLabel;

    fn deref<'a>(&'a self) -> &'a RealLabel {
        let &Label(ref inner) = self;
        inner.deref()
    }
}

impl LabelMaker for Label {
    fn new() -> Label {
        Label(Rc::new(RealLabel::new()))
    }
    fn from_const(val : u64) -> Label {
        Label(Rc::new(RealLabel::from_const(val)))
    }
    fn from_label(other : &Label) -> Label {
        let &Label(ref inner) = other;
        Label(Rc::new(RealLabel::from_label(inner.borrow())))
    }
    fn from_label_offset(other : &Label, offset : i64) -> Label {
        let &Label(ref inner) = other;
        Label(Rc::new(RealLabel::from_label_offset(inner.borrow(), offset)))
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

/// A reference to a `Label` that has been appended to a `Section`.
#[derive(Clone)]
struct Reference {
    /// The `Label` being referenced.
    label : Label,
    /// The offset of the reference within the `Section`.
    offset : u64,
    /// The endianness with which the `Label` should be stored.
    endian : Endian,
    /// The size with which the `Label` should be stored.
    size : usize,
}

/// A section is a sequence of bytes, constructed by appending bytes to the end.
///
/// Sections have a convenient and flexible set of member
/// functions for appending data in various formats: big-endian and
/// little-endian signed and unsigned values of different sizes, and
/// raw blocks of bytes.
///
/// See [the module-level documentation][module] for examples.
///
/// [module]: index.html
pub struct Section  {
    /// The current endianness of the writer.
    ///
    /// This sets the behavior of the D<N> appending functions.
    pub endian : Endian,
    /// The contents of the section.
    contents: Cursor<Vec<u8>>,
    references: Vec<Reference>,
}

impl Section {
    /// Construct a `Section` with platform-default endianness.
    pub fn new() -> Section {
        Section::with_endian(DEFAULT_ENDIAN)
    }

    /// Construct a `Section` with `endian` endianness.
    pub fn with_endian(endian : Endian) -> Section {
        Section {
            endian: endian,
            contents: Cursor::new(vec!()),
            references: vec!(),
        }
    }

    /// Return the current size of the section.
    pub fn size(&self) -> u64 {
        self.contents.get_ref().len() as u64
    }

    /// Get the contents of this section as a slice of bytes.
    ///
    /// Consumes the section. If there were still undefined labels,
    /// return `None`.
    pub fn get_contents(self) -> Option<Vec<u8>> {
        // Patch all labels into the section's contents.
        let mut section = self;
        let references : Vec<Reference> = section.references.iter().cloned().collect();
        let mut ok = true;
        section = references.iter().cloned().fold(section, |s, r| {
                if let Some(val) = r.label.value() {
                    s.store_label_value(val, r.offset, r.endian, r.size)
                } else {
                    ok = false;
                    s
                }
            });
        if ok {
            Some(section.contents.into_inner())
        } else {
            None
        }
    }

    /// Append `data` to the end of this section.
    ///
    /// Return this section.
    pub fn append_bytes(mut self, data : &[u8]) -> Section {
        self.contents.write_all(data).unwrap();
        self
    }

    /// Append `count` copies of `byte` to the end of this section.
    ///
    /// Return this section.
    pub fn append_repeated(mut self, byte : u8, count : usize) -> Section {
        for _ in 0..count {
            self.contents.write_u8(byte).unwrap();
        }
        self
    }

    fn store_label_value(mut self,
                         val : u64,
                         offset : u64,
                         endian: Endian,
                         size: usize) -> Section {
        let current = self.size();
        if offset != current {
            self.contents.seek(SeekFrom::Start(offset)).unwrap();
        }
        match endian {
            Endian::Little => {
                match size {
                    1 => self.L8(val as u8),
                    2 => self.L16(val as u16),
                    4 => self.L32(val as u32),
                    8 => self.L64(val),
                    _ => unreachable!("Unhandled label size!"),
                }
            },
            Endian::Big => {
                match size {
                    1 => self.B8(val as u8),
                    2 => self.B16(val as u16),
                    4 => self.B32(val as u32),
                    8 => self.B64(val),
                    _ => unreachable!("Unhandled label size!"),
                }
            },
        }
    }

    /// Append `label` to the Section with `endian` endianness, taking `size` bytes.
    ///
    /// Panics if `size` is not an intrinsic integer size: 1, 2, 4, 8 bytes.
    fn append_label(mut self,
                    label : &Label,
                    endian : Endian,
                    size : usize) -> Section {
        let current = self.size();
        // For labels with a known value, don't bother with a reference.
        if let Some(val) = label.value() {
            self.store_label_value(val, current, endian, size)
        } else {
            // label isn't yet known, need to store a reference.
            self.references.push(Reference {
                label: label.clone(),
                offset: current,
                endian: endian,
                size: size,
            });
            // Reserve space for the label.
            self.append_repeated(0, size)
        }
    }

    /// Append `byte` with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D8(mut self, byte : u8) -> Section {
        self.contents.write_u8(byte).unwrap();
        self
    }
    /// Append `label` as an u8 with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D8L(self, label : &Label) -> Section {
        let endian = self.endian;
        self.append_label(label, endian, 1)
    }
    /// Append `byte` as little-endian (identical to `D8`).
    ///
    /// Return this section.
    pub fn L8(self, byte : u8) -> Section { self.D8(byte) }
    /// Append `label` as a little-endian u8 (identical to `D8L`).
    ///
    /// Return this section.
    pub fn L8L(self, label : &Label) -> Section { self.D8L(label) }
    /// Append `byte` as big-endian (identical to `D8`).
    ///
    /// Return this section.
    pub fn B8(self, byte : u8) -> Section { self.D8(byte) }
    /// Append `label` as a big-endian u8 (identical to `D8L`).
    ///
    /// Return this section.
    pub fn B8L(self, label : &Label) -> Section { self.D8L(label) }

    /// Append `word` with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D16(self, word : u16) -> Section {
        match self.endian {
            Endian::Little => self.L16(word),
            Endian::Big => self.B16(word)
        }
    }
    /// Append `label` as an u16 with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D16L(self, label : &Label) -> Section {
        let endian = self.endian;
        self.append_label(label, endian, 2)
    }
    /// Append `word` as little-endian.
    ///
    /// Return this section.
    pub fn L16(mut self, word : u16) -> Section {
        self.contents.write_u16::<LittleEndian>(word).unwrap();
        self
    }
    /// Append `label` as a little-endian u16.
    ///
    /// Return this section.
    pub fn L16L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Little, 2)
    }
    /// Append `word` as big-endian.
    ///
    /// Return this section.
    pub fn B16(mut self, word : u16) -> Section {
        self.contents.write_u16::<BigEndian>(word).unwrap();
        self
    }
    /// Append `label` as a big-endian u16.
    ///
    /// Return this section.
    pub fn B16L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Big, 2)
    }

    /// Append `dword` with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D32(self, dword : u32) -> Section {
        match self.endian {
            Endian::Little => self.L32(dword),
            Endian::Big => self.B32(dword)
        }
    }
    /// Append `label` as an u32 with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D32L(self, label : &Label) -> Section {
        let endian = self.endian;
        self.append_label(label, endian, 4)
    }
    /// Append `dword` as little-endian.
    ///
    /// Return this section.
    pub fn L32(mut self, dword : u32) -> Section {
        self.contents.write_u32::<LittleEndian>(dword).unwrap();
        self
    }
    /// Append `label` as a little-endian u32.
    ///
    /// Return this section.
    pub fn L32L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Little, 4)
    }
    /// Append `dword` as big-endian.
    ///
    /// Return this section.
    pub fn B32(mut self, dword : u32) -> Section {
        self.contents.write_u32::<BigEndian>(dword).unwrap();
        self
    }
    /// Append `label` as a big-endian u32.
    ///
    /// Return this section.
    pub fn B32L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Big, 4)
    }

    /// Append `qword` with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D64(self, qword : u64) -> Section {
        match self.endian {
            Endian::Little => self.L64(qword),
            Endian::Big => self.B64(qword)
        }
    }
    /// Append `label` as an u64 with the Section's default endianness.
    ///
    /// Return this section.
    pub fn D64L(self, label : &Label) -> Section {
        let endian = self.endian;
        self.append_label(label, endian, 8)
    }
    /// Append `qword` as little-endian.
    ///
    /// Return this section.
    pub fn L64(mut self, qword : u64) -> Section {
        self.contents.write_u64::<LittleEndian>(qword).unwrap();
        self
    }
    /// Append `label` as a little-endian u64.
    ///
    /// Return this section.
    pub fn L64L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Little, 8)
    }
    /// Append `qword` as big-endian.
    ///
    /// Return this section.
    pub fn B64(mut self, qword : u64) -> Section {
        self.contents.write_u64::<BigEndian>(qword).unwrap();
        self
    }
    /// Append `label` as a big-endian u64.
    ///
    /// Return this section.
    pub fn B64L(self, label : &Label) -> Section {
        self.append_label(label, Endian::Big, 8)
    }
}

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
    let b_f3 = Rc::new(Binding::from(b_f1.clone(), 10));
    assert_eq!(b_f3.offset(&b_u).unwrap(), 10);
    let b_f4 = Rc::new(Binding::from(b_f3.clone(), 10));
    assert_eq!(b_f4.offset(&b_u).unwrap(), 20);
}

#[test]
fn binding_value() {
    let b_u = Rc::new(Binding::unconstrained());
    let b_c = Rc::new(Binding::constant(1));
    let b_f1 = Rc::new(Binding::from(b_u.clone(), 0));
    assert!(b_u.value().is_none());
    assert_eq!(b_c.value().unwrap(), 1);
    assert!(b_f1.value().is_none());

    let b_f2 = Rc::new(Binding::from(b_c.clone(), 10));
    assert_eq!(b_f2.value().unwrap(), 11);
    // We need to go deeper.
    let b_f3 = Rc::new(Binding::from(b_f1.clone(), 10));
    assert!(b_f3.value().is_none());
    let b_f4 = Rc::new(Binding::from(b_f3.clone(), 10));
    assert!(b_f4.value().is_none());

    let b_f5 = Rc::new(Binding::from(b_f2.clone(), 10));
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
    let s = Section::new();
    let b1 = [0, 1, 2, 3, 4];
    let b2 = [0xf, 0xe, 0xd, 0xc, 0xb];
    assert_eq!(s.append_bytes(&b1).append_bytes(&b2).get_contents().unwrap(),
               &[0, 1, 2, 3, 4, 0xf, 0xe, 0xd, 0xc, 0xb]);
}

#[test]
fn section_append_repeated() {
    let s = Section::new();
    assert_eq!(s.append_repeated(0xff, 5).get_contents().unwrap(),
               &[0xff, 0xff, 0xff, 0xff, 0xff]);
}

#[test]
fn section_test_8() {
    let s = Section::new();
    assert_eq!(s.D8(0x12).L8(0x12).B8(0x12).get_contents().unwrap(),
               &[0x12, 0x12, 0x12]);
}

#[test]
fn section_test_16() {
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D16(0xABCD).L16(0xABCD).B16(0xABCD).get_contents().unwrap(),
               &[0xCD, 0xAB,
                 0xCD, 0xAB,
                 0xAB, 0xCD]);
}

#[test]
fn section_test_32() {
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D32(0xABCD1234).L32(0xABCD1234).B32(0xABCD1234)
               .get_contents().unwrap(),
               &[0x34, 0x12, 0xCD, 0xAB,
                 0x34, 0x12, 0xCD, 0xAB,
                 0xAB, 0xCD, 0x12, 0x34]);
}

#[test]
fn section_test_64() {
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D64(0x12345678ABCDEFFF)
               .L64(0x12345678ABCDEFFF)
               .B64(0x12345678ABCDEFFF)
               .get_contents().unwrap(),
               &[0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56, 0x34, 0x12,
                 0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56, 0x34, 0x12,
                 0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF, 0xFF]);
}


#[test]
fn section_d8l_const_label() {
    let l = Label::from_const(10);
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D8L(&l).L8L(&l).B8L(&l)
               .get_contents().unwrap(),
               &[10, 10, 10]);
}

#[test]
fn section_d16l_const_label() {
    let l = Label::from_const(0xABCD);
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D16L(&l).L16L(&l).B16L(&l)
               .get_contents().unwrap(),
               &[0xCD, 0xAB, 0xCD, 0xAB, 0xAB, 0xCD]);
}

#[test]
fn section_d32l_const_label() {
    let l = Label::from_const(0xABCD1234);
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D32L(&l).L32L(&l).B32L(&l)
               .get_contents().unwrap(),
               &[0x34, 0x12, 0xCD, 0xAB,
                 0x34, 0x12, 0xCD, 0xAB,
                 0xAB, 0xCD, 0x12, 0x34]);
}

#[test]
fn section_d64l_const_label() {
    let l = Label::from_const(0xABCD12345678F00D);
    let s = Section::with_endian(Endian::Little);
    assert_eq!(s.D64L(&l).L64L(&l).B64L(&l)
               .get_contents().unwrap(),
               &[0x0D, 0xF0, 0x78, 0x56, 0x34, 0x12, 0xCD, 0xAB,
                 0x0D, 0xF0, 0x78, 0x56, 0x34, 0x12, 0xCD, 0xAB,
                 0xAB, 0xCD, 0x12, 0x34, 0x56, 0x78, 0xF0, 0x0D]);
}

#[test]
fn section_get_contents_label_no_value() {
    // Trying to get_contents on a Section when a Label that was added
    // has no value should return None.
    let l = Label::new();
    let s = Section::with_endian(Endian::Little);
    assert!(s.D8L(&l).get_contents().is_none());
}

#[test]
fn section_label_assign_late() {
    let l = Label::new();
    let mut s = Section::with_endian(Endian::Little);
    s = s.D8L(&l).L8L(&l).B8L(&l);
    // Now assign a value to l.
    l.set_const(10);
    assert_eq!(s.get_contents().unwrap(),
               &[10, 10, 10]);
}


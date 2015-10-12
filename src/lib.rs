// Copyright 2015 Ted Mielczarek. See the COPYRIGHT
// file at the top-level directory of this distribution.

//! A set of types for building complex binary streams.
//!
//! For testing code that consumes binary data, it is necessary to
//! be able to generate test inputs consisting of various valid and
//! invalid permutations. The `Section` struct defined in this crate
//! allows for easily building a stream of bytes in any desired
//! endianness.

#![allow(non_snake_case)]

extern crate byteorder;

use std::io::Cursor;
use std::io::Write;

use byteorder::{ByteOrder,BigEndian,LittleEndian,WriteBytesExt};

/// Possible byte orders
#[derive(Debug, PartialEq)]
pub enum Endian {
    Big,
    Little,
}


#[cfg(target_endian = "little")]
pub const DEFAULT_ENDIAN : Endian = Endian::Little;

#[cfg(target_endian = "big")]
pub const DEFAULT_ENDIAN : Endian = Endian::Big;

/// A section is a sequence of bytes, constructed by appending bytes to the end.
///
/// Sections have a convenient and flexible set of member
/// functions for appending data in various formats: big-endian and
/// little-endian signed and unsigned values of different sizes, and
/// raw blocks of bytes.
///
/// The methods for writing data all return a reference to the `Section`
/// so that they can be chained, like:
///
/// ```
/// use test_assembler::Section;
///
/// let mut section = Section::new();
/// section.D8(0xFF)
///    .L16(0xABCD)
///    .B32(0x12345678);
/// assert_eq!(section.get_contents().unwrap(),
///            &[0xFF, 0xCD, 0xAB, 0x12, 0x34, 0x56, 0x78]);
/// ```
pub struct Section  {
    /// The current endianness of the writer.
    ///
    /// This sets the behavior of the D<N> appending functions.
    pub endian : Endian,
    /// The contents of the section.
    contents: Cursor<Vec<u8>>,
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
            // Box::new(EndianLessNessReader::<LittleEndian>::new(
            contents: Cursor::new(vec!()),
        }
    }

    /// Get the contents of this section as a slice of bytes.
    ///
    /// If there were still undefined labels, return `None`.
    pub fn get_contents(&self) -> Option<&[u8]> {
        // TODO: when we support labels, patch them in.
        Some(self.contents.get_ref())
    }

    /// Append `data` to the end of this section.
    ///
    /// Return a reference to this section.
    pub fn append_bytes(&mut self, data : &[u8]) -> &mut Section {
        self.contents.write_all(data).unwrap();
        self
    }

    /// Append `count` copies of `byte` to the end of this section.
    ///
    /// Return a reference to this section.
    pub fn append_repeated(&mut self, byte : u8, count : usize) -> &mut Section {
        for _ in 0..count {
            self.contents.write_u8(byte).unwrap();
        }
        self
    }

    /// Append `byte` with the Section's default endianness.
    ///
    /// Return a reference to this section.
    pub fn D8(&mut self, byte : u8) -> &mut Section {
        self.contents.write_u8(byte).unwrap();
        self
    }
    /// Append `byte` as little-endian (identical to `D8`).
    ///
    /// Return a reference to this section.
    pub fn L8(&mut self, byte : u8) -> &mut Section { self.D8(byte) }
    /// Append `byte` as big-endian (identical to `D8`).
    ///
    /// Return a reference to this section.
    pub fn B8(&mut self, byte : u8) -> &mut Section { self.D8(byte) }

    /// Append `word` with the Section's default endianness.
    ///
    /// Return a reference to this section.
    pub fn D16(&mut self, word : u16) -> &mut Section {
        match self.endian {
            Endian::Little => self.L16(word),
            Endian::Big => self.B16(word)
        }
    }
    /// Append `word` as little-endian.
    ///
    /// Return a reference to this section.
    pub fn L16(&mut self, word : u16) -> &mut Section {
        self.contents.write_u16::<LittleEndian>(word).unwrap();
        self
    }
    /// Append `word` as big-endian.
    ///
    /// Return a reference to this section.
    pub fn B16(&mut self, word : u16) -> &mut Section {
        self.contents.write_u16::<BigEndian>(word).unwrap();
        self
    }

    /// Append `dword` with the Section's default endianness.
    ///
    /// Return a reference to this section.
    pub fn D32(&mut self, dword : u32) -> &mut Section {
        match self.endian {
            Endian::Little => self.L32(dword),
            Endian::Big => self.B32(dword)
        }
    }
    /// Append `dword` as little-endian.
    ///
    /// Return a reference to this section.
    pub fn L32(&mut self, dword : u32) -> &mut Section {
        self.contents.write_u32::<LittleEndian>(dword).unwrap();
        self
    }
    /// Append `dword` as big-endian.
    ///
    /// Return a reference to this section.
    pub fn B32(&mut self, dword : u32) -> &mut Section {
        self.contents.write_u32::<BigEndian>(dword).unwrap();
        self
    }

    /// Append `qword` with the Section's default endianness.
    ///
    /// Return a reference to this section.
    pub fn D64(&mut self, qword : u64) -> &mut Section {
        match self.endian {
            Endian::Little => self.L64(qword),
            Endian::Big => self.B64(qword)
        }
    }
    /// Append `qword` as little-endian.
    ///
    /// Return a reference to this section.
    pub fn L64(&mut self, qword : u64) -> &mut Section {
        self.contents.write_u64::<LittleEndian>(qword).unwrap();
        self
    }
    /// Append `qword` as big-endian.
    ///
    /// Return a reference to this section.
    pub fn B64(&mut self, qword : u64) -> &mut Section {
        self.contents.write_u64::<BigEndian>(qword).unwrap();
        self
    }
}

#[test]
fn construction() {
    let s = Section::new();
    assert_eq!(s.endian, DEFAULT_ENDIAN);

    let s2 = Section::with_endian(Endian::Little);
    assert_eq!(s2.endian, Endian::Little);
}

#[test]
fn append_bytes() {
    let mut s = Section::new();
    let b1 = [0, 1, 2, 3, 4];
    let b2 = [0xf, 0xe, 0xd, 0xc, 0xb];
    s.append_bytes(&b1).append_bytes(&b2);
    assert_eq!(s.get_contents().unwrap(),
               &[0, 1, 2, 3, 4, 0xf, 0xe, 0xd, 0xc, 0xb]);
}

#[test]
fn append_repeated() {
    let mut s = Section::new();
    s.append_repeated(0xff, 5);
    assert_eq!(s.get_contents().unwrap(),
               &[0xff, 0xff, 0xff, 0xff, 0xff]);
}

#[test]
fn test_8() {
    let mut s = Section::new();
    s.D8(0x12)
        .L8(0x12)
        .B8(0x12);
    assert_eq!(s.get_contents().unwrap(),
               &[0x12, 0x12, 0x12]);
}

#[test]
fn test_16() {
    let mut s = Section::with_endian(Endian::Little);
    s.D16(0xABCD)
        .L16(0xABCD)
        .B16(0xABCD);
    assert_eq!(s.get_contents().unwrap(),
               &[0xCD, 0xAB,
                 0xCD, 0xAB,
                 0xAB, 0xCD]);
}

#[test]
fn test_32() {
    let mut s = Section::with_endian(Endian::Little);
    s.D32(0xABCD1234)
        .L32(0xABCD1234)
        .B32(0xABCD1234);
    assert_eq!(s.get_contents().unwrap(),
               &[0x34, 0x12, 0xCD, 0xAB,
                 0x34, 0x12, 0xCD, 0xAB,
                 0xAB, 0xCD, 0x12, 0x34]);
}

#[test]
fn test_64() {
    let mut s = Section::with_endian(Endian::Little);
    s.D64(0x12345678ABCDEFFF)
        .L64(0x12345678ABCDEFFF)
        .B64(0x12345678ABCDEFFF);
    assert_eq!(s.get_contents().unwrap(),
               &[0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56, 0x34, 0x12,
                 0xFF, 0xEF, 0xCD, 0xAB, 0x78, 0x56, 0x34, 0x12,
                 0x12, 0x34, 0x56, 0x78, 0xAB, 0xCD, 0xEF, 0xFF]);
}

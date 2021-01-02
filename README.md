![Continuous integration](https://github.com/luser/rust-test-assembler/workflows/Continuous%20integration/badge.svg) (https://coveralls.io/github/luser/rust-test-assembler?branch=master) [![crates.io](https://img.shields.io/crates/v/test-assembler.svg)](https://crates.io/crates/test-assembler) [![](https://docs.rs/test-assembler/badge.svg)](https://docs.rs/test-assembler)

# Overview

This Rust crate implements a set of types for building complex binary streams, primarily for writing tests of things that ingest binary data.

[Documentation for master](http://luser.github.io/rust-project-docs/test-assembler/test_assembler/)

# Example

``` rust
extern crate test_assembler;

use test_assembler::*;

fn main() {
  // Create some `Label`s, which can be used to fill in values that aren't yet known,
  // or marked to provide offsets into data in a `Section`.
  let l1 = Label::new();
  let l2 = Label::new();
  // `Section`s can be created with either default endianness.
  let s = Section::with_endian(Endian::Little);
  // `start` is a `Label` whose value is the beginning of the `Section`'s data.
  let start = s.start();
  let s = s.append_bytes(&[0x01, 0x02, 0x03])
    // Append a 32-bit word with the section's default endianness
    // Methods on `Section` chain to make writing repeated entries simple!
    .D32(0xabcd0102)
    // L1 will now have the value of the current offset into the section.
    .mark(&l1)
    // Append the value of the `Label` l2 as a 16-bit word in big-endian
    .B16(&l2)
    // Append 10 bytes of 0xff.
    .append_repeated(0xff, 10);
  // Labels that have been added to Sections need to have a fixed value before
  // you call `Section::get_contents`. Calling `Section::mark` will do that,
  // or you can give them a constant value.
  l2.set_const(0x1234);
  let bytes = s.get_contents().unwrap();
  // By default the `start` Label doesn't have a const value, but you can do math
  // on Labels that have relative offsets!
  let offset = &l1 - &start;
  assert_eq!(7, offset);
  let i = offset as usize;
  // Label values that appended have their value inserted when `Section::get_contents`
  // is called, so they can depend on things that aren't known at insertion time.
  assert_eq!(&[0x12, 0x34], &bytes[i..i + 2]);
}
```

# License

This software is provided under the MIT license. See [LICENSE](LICENSE).

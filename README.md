[![Continuous integration](https://github.com/luser/rust-test-assembler/actions/workflows/rust.yml/badge.svg)](https://github.com/luser/rust-test-assembler/actions/workflows/rust.yml) [![crates.io](https://img.shields.io/crates/v/test-assembler.svg)](https://crates.io/crates/test-assembler) [![](https://docs.rs/test-assembler/badge.svg)](https://docs.rs/test-assembler)

# Overview

This Rust crate implements a set of types for building complex binary streams, primarily for writing tests of things that ingest binary data. It's designed to allow you to create input data with specific properties that might be otherwise difficult to produce. For example, testing data in big-endian byte ordering on little-endian systems, testing your error-handling code by producing inputs that are malformed in certain ways, or testing code that parses a piece of a larger overall format without having to generate the whole thing.

You use this crate primarily by creating a `Section`, which provides APIs to build a sequence of bytes piece-by-piece. In addition to using fixed data inputs, you can also insert the contents of `Label`s, which are placeholders for values that are not yet known. These can be used to insert data calculated from elsewhere, such as offsets into the `Section` being built. When you're finished, you can call `Section::get_contents()` to produce a `Vec<u8>` of the contents.

# Example

``` rust
  use test_assembler::*;

  // Create some `Label`s, which can be used to fill in values that aren't yet known,
  // or marked to provide offsets into data in a `Section`.
  let l1 = Label::new();
  let l2 = Label::new();
  // `Section`s have an associated default endianness.
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
```

For examples of real-world usage, you can take a look at [various tests in the `gimli` crate](https://github.com/gimli-rs/gimli/blob/13c526510d0b0f5fab4ddb9a9abc0318cb142754/src/read/str.rs#L287), [the stack unwinding tests in the `minidump` crate](https://github.com/luser/rust-minidump/blob/330e4956f283d297ce09e7d122e9770b6d763336/minidump-processor/src/stackwalker/x86_unittest.rs#L75), or [the synth_minidump tests in the `minidump` crate](https://github.com/luser/rust-minidump/blob/master/minidump/src/synth_minidump.rs), which also demonstrate building test fixtures using this crate to build more complex structured data.

# License

This software is provided under the MIT license. See [LICENSE](LICENSE).

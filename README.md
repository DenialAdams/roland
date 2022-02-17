# Roland
Roland is a work-in-progress programming language. Roland was originally created for edification, but I hope that it can become something more production ready.

If you're still interested in trying Roland, I highly recommend doing so with WASM-4, as that currently provides the most complete experience. Read on to find out more.

## Getting the compiler

Roland does not yet have an official release cycle. However, I do publish binaries built from the most recent git commit:

Linux: http://www.brick.codes/roland/rolandc
Windows: http://www.brick.codes/roland/rolandc.exe

Alternatively, you can build `rolandc` yourself by running `cargo build --release` and taking the binary out of the `target/release/` directory.

## Informal Specification

Roland is a procedural programming language roughly at the level of C. If you have experience programming in any C-like language, you won't find much surprising here. That being said, here I'll enumerate the fundamentals and notable features.

Syntax wise, Roland looks a lot like Rust. This is just because thats what I have the most experience with - **the syntax could change in the future.**

### Types

The following primitive types are supported:

- `u8`
- `u16`
- `u32`
- `u64`
- `usize`
- `i8`
- `i16`
- `i32`
- `i64`
- `isize`
- `f32`
- `f64`
- `bool`

Each numeric type is identified by a prefix: **u**nsigned integer, signed **i**nteger, and **f**loat, followed by the width in bits. `usize` and `isize` are type safe aliases for whatever the pointer width is on your target.

Pointer types are an `&` followed by a type. For instance, `&u8` is a pointer to an unsigned 8-bit integer.

Array types are composed of a type and an element count. This means that the element count must be known at compile time, as it's part of the type. For instance, `[f32; 10]` is an array of 10 32-bit floating point numbers.

#### User-defined types

There are two ways to define new types in Roland: `enum`s and `struct`s.

```roland
enum MyEnum {
   VariantA,
   VariantB
}

struct MyStruct {
   field_one: u8,
   field_two: MyEnum,
}

proc main() {
   let x = MyEnum::VariantB;
   let y = MyStruct {
      field_one: 10,
      field_two: x,
   };
}
```

Roland will re-order struct fields to minimize padding, so it's not a good idea to rely on the order (i.e. by passing the struct to an external API.)

#### Strings

`String` is a struct defined in the standard library that looks like this:

```roland
struct String {
   pointer: &u8,
   length: usize,
}
```

String literals become instances of `String` and are encoded as UTF-8. And string support in the standard library will assume UTF-8 encoding in the future.

You can make your own strings just like you can create an instance of any struct.

### Looping

Roland currently supports two ways to loop. The first way is just by declaring a `loop` block that will inifinitely loop until broken out of:

```roland
loop {
   // ...
}
```

The second is to loop over a range of values:

```roland
let my_array = [true, false, true];
for x in 0..my_array.length {
   // x will be 0, then 1, then 2.
   my_array[x] = !my_array[x];
}
```

### Procedures

Procedures are defined with the keyword `proc`, and can be called like you expect:

```roland
proc reticulate_splines(x: u64) {
   // ...
}

proc main() {
   reticulate_splines(10);
}
```

Roland also supports named parameters:

```roland
proc do_something_with_options(named also_do_something_else: bool, named also_do_other_thing: bool) {
   // ...
}

proc main() {
   do_something_with_options(also_do_other_thing: true, also_do_something_else: false);
}
```

## Compilation Targets

Roland currently supports compiling to two different flavors of WebAssembly.

### WASI
This is the default target. A `.wat` file is emitted that can be run directly with `wasmtime`.

The only WASI API we support at the moment is printing text to stdout, through the function `print`.

### WASM-4
By providing the `--wasm4` flag to the roland compiler, you'll instead compile for [WASM-4](https://wasm4.org/). A `.wasm` file is emitted that can be directly provided to `w4 run`.

When compiling for the wasm-4 target, all wasm-4 APIs will be automatically made available to you. No extra configuration is needed.

An example WASM-4 game can be viewed here: https://github.com/DenialAdams/InfiniteRunner/blob/master/endless-runner.rol

## Tooling

### Syntax Highlighting
You can find syntax highlighting for Roland on the vscode marketplace - search for "Roland", and it's the extension published by "brick.codes".

### Live editor
You can compile Roland in the browser at https://www.brick.codes/roland/.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

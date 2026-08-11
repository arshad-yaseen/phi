# Changelog

## [Unreleased]

### Language

- A narrower number lands on a wider one with nothing written, because every
  value of the narrower type is already a value of the wider. Signedness may
  change where no value is lost, an `f32` is exactly an `f64`, and the two ends
  of an operator meet the same way, so a `u32` counter reaches a `u64` length
  with no conversion between them.
- `@int_cast(n)` is the conversion that can lose a value, and answers `T | none`,
  so `or` says what happens when it does not fit. It converts to what it lands
  on, and takes `[T]` where nothing lands it.
- An operation the compiler performs itself is written `@name`, so `intrinsic`
  is no longer a keyword. Only one that could break a guarantee the checker
  made, `@ptr_cast`, is still the standard library's alone.
- Reaching a member by the wrong kind is refused: calling a field used to
  compile silently, reading a method now says to call it, and a missed name
  suggests methods as well as fields.
- Every type answers its size and alignment: `bool` is one byte, and
  `*T | none` is one word, with `none` as the zero no valid pointer holds.
  A type past 4 GiB is refused with `E0261`.
- A string is bytes and a character is a number, both written as constants that
  fit where their values fit: `"text/plain"` returned as `[]u8` is bytes the
  program owns, `let magic: [2]u8 = "hi"` is storage with its length checked,
  and `s[i] == 'a'` compares two numbers. Escapes decode at compile time, and a
  literal never crosses a line.
- `@size_of[T]()`, `@align_of[T]()`, `@min_int[T]()`, and `@max_int[T]()` answer
  as constants that fit wherever their value fits, so `let n: u32 =
  @size_of[Node]()` needs no conversion and `@max_int[u64]()` is exact.
- `std.mem` opens the standard library with `align_up`, which rounds an address
  to an alignment it asserts is a power of two.
- `std.debug.assert(ok)` arrives over `@trap()`: a violated contract stops the
  program where it stands. `std.math` opens with `is_power_of_two`.
- A union may stand in a bracket, so `Box[u32 | none]` means the union it
  spells.
- The prelude arrives: `none`, `true`, `false`, `bool`, and `str` are declared
  once in `std.prelude` and visible in every file, so optionals, truth, and
  text share one identity across modules. A file's own declaration still wins.
- What a call feeds may pin its type argument: in `let a: u64 =
  mem.align_up(11, 8)`, the annotation decides `T` where the arguments
  leave it open. An argument pins through whatever its parameter is
  written in, so `T`, `*T`, `[]T`, and `[N]T` all read what they hold,
  and every parameter written in it is read until one has a type to give,
  so a bare number may sit beside the argument that pins it. The return
  type reads the same way, so an annotation reaches a type argument no
  parameter mentions. A width stated nowhere still refuses.
- `[N]T` is an array, N values of one type laid out end to end and written
  `[1, 2, 3]`. The length lives in the type, so it costs no memory, answers as
  `a.len`, and may size another array. A literal has no type until it lands, so
  one written once fits wherever its value fits. `a[i]` names an element, which
  is read, written, and pointed at the way a field is, and a constant index past
  the end is refused before anything runs, while every other index is checked
  before the memory is touched.
- `[]T` is a view of elements it does not own, two words wide, and `[]var T`
  also writes through and fits wherever a `[]T` is asked. It answers `len` and
  indexes the way an array does, holds no elements so a type may hold a view of
  itself, and `[]T | none` costs no more than the view alone.
- A constant that lands on a view gets bytes the program owns, so `[2, 3, 5, 7]`
  fits a `[]u32` and one written twice is one set of bytes. It never fits a
  `[]var T`, and an array with a part settled at run time is refused rather
  than viewed from a frame that is about to leave.
- `a[x..y]` makes one, the single bridge from storage to a view, spelled as an
  expression so a reader sees the moment it happens. `a..` runs to the base's
  own length, the ends take each other's type, what the view may write is what
  the place it came from allowed, and a range that leaves its base is refused
  before anything runs, or checked before the view is made.
- `loop i in 0..n` counts a range: the name is a `let` for the pass, both ends
  are read once before the first, and the counter takes the type of the ends,
  `u64` where neither says. `in` joins the keywords.
- A struct literal may leave out the type where what it lands on says it, so
  `let p: Point = .{ x: 1, y: 2 }` reads once instead of twice, as do an
  argument, a return, a field, and an element. It still names the type where
  nothing lands it, and where what lands it is a union.
- A literal folds where its parts are constant, whether it builds an array or a
  struct, so `Point.{ x: 1, y: 2 }` binds at the top level, sits inside an
  array, and costs no instruction, while one with a runtime part is built where
  it stands.
- A `var` no longer asks a sealed constant for the type it already carries:
  `let n: u64 = 2` followed by `var c = n` used to be refused.

### Compiler

- A shift is bounded by the width it shifts rather than the width constants
  fold in, so `a << 9` on a `u8` says that a `u8` shifts by 0 to 7.
- A `break` carrying a value that never arrives leaves its loop's type to the
  arms that do, the way every other branch already worked.
- `E0248` retires. It named a byte a number cannot contain, which the
  tokenizer never puts inside one, so no program could reach it. What it
  described is `E0247` along with every other malformed number.

## [0.2.0] - 2026-08-08

The language is now Phi: the binary is `phi`, and a source file ends in
`.phi`. It is redesigned around one idea: a type may be several types, and
a branch that settles which one narrows the value to it, so optionals,
errors, and sum types stop being three features and become one. This
release removes what that idea replaces and builds the rest on unions.

### Language

- `type Timeout` declares a unit type, a type whose only value is its name.
- `A | B` is a union type: members are distinct, order is part of the type,
  and a member that is itself a union flattens in place, so aliases compose.
- A value enters a union by membership, unwrapped, and comes back out only
  through a branch that proves the member.
- A condition is a union asking whether it holds its first member, so `if`,
  `and`, and `or` all branch on that one question.
- `e is T` tests which member a union holds and narrows the tested name: in
  both branches, across `and`, and past a branch that leaves.
- `e or f` is the first member of `e`, or else `f`: `or 8080` substitutes,
  `or return` propagates, `or e { ... }` handles, and on a `bool` it stays
  logical or.
- `match` splits a union into one arm per member, exhaustive by counting,
  and `else` is the rest as a type rather than a blind default.
- `bool` left the compiler: `type bool = true | false` is a declaration
  like any other, found by name where a truth value is written.
- An alias may be generic: `type Maybe[T] = T | none` instantiates wherever
  a type is written, and `Maybe[u32]` is `u32 | none` exactly.
- An annotation seals a constant, so `let b: u64 = 2` is a `u64` everywhere
  it goes, the way Zig, Rust, and Go read it. A bare literal still takes
  any type its value fits.
- Gone: optionals `?T`, error unions `!T`, `error Name`, `try`, `catch`,
  `orelse`, `null`, and the `|v|` capture. A union and `or` are all of
  them, with nothing wrapped.
- `loop` replaces `while`: `loop { }` runs until a `break`, `loop cond { }`
  while the condition holds, a label reaches an outer loop, and `break v`
  with `else` makes a loop an expression.
- `type X = { }` replaces `struct X { }`: one keyword declares a struct, a
  union, an alias, or a unit.
- A struct literal names the type it builds, `Point.{ x: 1 }`, and the bare
  `.{ }` is gone.
- `use` is now `import`, and prefix `!` is now `not`.
- New operators: bitwise `&`, `|`, `^`, `~`, `<<`, `>>`, compound
  assignment, `p.*` to read through a pointer, and `a[i]` to index.
- `intrinsic` is a keyword only the standard library reaches, and
  `intrinsic.ptr_cast[T](p)` retypes a pointer without loosening it.
- A method without `pub` is private to its file, the way every other
  declaration already was.

### Compiler

- A parse error stops nothing: the parser reads the whole file, and the
  declarations that survive recovery are checked and importable.
- Function bodies check from a flat worklist, so a call chain of any depth
  compiles.
- Output is deterministic: diagnostics print in file order, and `phi ir`
  prints functions in the order the program first needed them.
- Number literals are validated exactly, hex floats included, each mistake
  with its own message.
- Edges that crashed now report: `-x` on the smallest signed value, and
  `&` in a top-level binding.
- `E0216`, `E0217`, and `E0224` through `E0229` retire with the features
  they policed.

### Command line

- Both commands close with `checked in 1.234ms` on standard error, measured
  from reading the entry to the end of compilation.

### Distribution

- Every commit on `main` that passes CI is published as a dev build at the
  `dev` tag, with an `index.json` naming the version, the commit, and every
  checksum. Numbered releases stay the only supported builds.

## [0.1.0] - 2026-08-04

Initial release. `phi` checks a program and prints its typed IR. Nothing runs yet.

### Language

- Structs with fields and methods, and generics written `[T]`.
- `let` and `var` bindings, `if`/`else`, `while`, and `defer`.
- `if`, `return`, `break`, and `continue` in value positions.
- Optionals `?T` and error unions `!T`, with `try`, `catch`, and `orelse`.
- Pointers `*T` to read through and `*var T` to write through.
- Arenas through `std.mem.Arena`, the only way to allocate.
- Modules are files, imported with `use` and exported with `pub`.

### Compiler

- Parsing with recovery.
- Demand-driven analysis, memoized per declaration.
- A typed control flow graph per function.
- Diagnostics with stable codes, spans, and suggestions.

### Command line

- `phi check <entry>` and `phi ir <entry>`.
- `--std <dir>`, `--color auto|on|off`, and `--version`.

[Unreleased]: https://github.com/arshad-yaseen/phi/compare/0.2.0...HEAD
[0.2.0]: https://github.com/arshad-yaseen/phi/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/arshad-yaseen/phi/releases/tag/0.1.0

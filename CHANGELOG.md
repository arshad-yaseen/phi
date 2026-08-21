# Changelog

## [Unreleased]

### Language

- A settled `if` or `match` picks its arm before anything runs, and stands in a
  top-level `let` and in a type.
- `std/sys` is where the standard library reaches the operating system.
- `std/sys/c` names the C integer types and the calls std reaches the system
  through.
- `std/target` names the operating system, the architecture, and the width of an
  address.
- A field without `pub` is private to its file.
- `@view(p, n)` is a view of `n` elements at a pointer, and `@int_from_ptr(p)`
  is its address.
- `@splat` is now `@repeat`.
- `std/mem` gains `fill`, which sets every element of a view to one value.
- `std/sys` hands out pages with `page_size`, `alloc_pages`, and `free_pages`.
- `@compile_error("why")` refuses a build wherever it is reached.
- `@int_cast(n)` converts, and stops the program where the type does not hold
  the value.
- `@int_fits(n)` is the `T | none` answer `@int_cast` used to give.
- `io.print` finishes a run of bytes too long for one write.
- `std/math` gains `min`, the smaller of two integers.
- `mem.eql` is now `mem.equal`.
- `std/fmt` writes a number as decimal digits into a buffer the caller owns.
- `io.format_max` is now `fmt.decimal_max`.

### Compiler

- A view is laid out as an address and a `u64` count.
- An arm of an `if`, a loop, or a `match` naming a type where a value belongs is
  refused.
- A struct holding a unit type, or an array of one, builds to a binary.
- `x or return` with a broken `x` reports `x` alone.
- `E0267` is a union that was not narrowed, wherever one is reached into,
  assigned, or handed on.
- A match arm that covers the whole union, `else` included, no longer stops the
  compiler.

### Command line

- `--target <arch>-<os>` says what to build for, and `wasm32-wasi` joins the six
  native targets.
- `phi run` retires.

## [0.4.0] - 2026-08-18

`phi build` compiles a program through C to a native binary, starting at
`fn main()`. A generic can ask what its type argument is, and a bound holds it
to a set of types.

### Language

- `import a/b` names a module, and `as` renames what it binds.
- A program starts at `fn main()` in its entry file.
- `extern fn` declares a function the linker finds elsewhere.
- `@splat(v)` is an array whose every element is `v`.
- A run of lines opening with `\\` is one string.
- A view answers `.ptr` beside `.len`.
- `is` and `match` fold where the union is already settled.
- `T is u32` asks whether two types are the same, and `match T` picks the arm
  labelled with the type it is.
- A type parameter may be bounded, `fn abs[T: Number](n: T) T`.
- `is` takes a union on its right, `r is Timeout | NotFound`.
- An integer reaches a float wherever every value of it is exact.
- `type X = { }` with nothing inside is refused.
- A top-level binding takes whatever settles before anything runs.
- A value enters a union through whatever edge its member would have taken.
- `str` leaves the prelude, and text is written as `[]u8`.
- `std/io` gains `print` and `format`, and the prelude gains `Signed`,
  `Unsigned`, `Integer`, `Float`, and `Number`.

### Compiler

- A header that leaves makes what follows the construct unreachable.
- The arms of an `if`, a loop, or a `match` used as a value name its type
  between them in whichever order they come.
- An operator refused on a union says how to narrow it.
- A type parameter written `[]T` is pinned by a literal.
- A report from inside a long chain of instantiations keeps both ends of it.
- A type standing where a value belongs is refused.

### Command line

- `phi build` compiles the program to a native binary, `phi run` builds and then
  runs it, and `--opt fast|small` says what the C compiler favours.

## [0.3.0] - 2026-08-11

Programs gain storage: `[N]T` lays values end to end, `[]T` views values it does
not own, and every type answers its size and alignment. A standard library opens
on top of a prelude.

### Language

- `[N]T` is an array, N values of one type laid out end to end.
- `[]T` is a view of elements it does not own, and `[]var T` also writes through.
- `a[x..y]` is the one bridge from storage to a view.
- A constant that lands on a view gets bytes the program owns.
- A string is bytes and a character is a number.
- `loop i in 0..n` counts a range.
- Every type answers its size and alignment, and one past 4 GiB is refused.
- A narrower number lands on a wider one with nothing written.
- `@int_cast(n)` is the conversion that can lose a value, and answers `T | none`.
- An operation the compiler performs itself is written `@name`.
- `@size_of[T]()`, `@align_of[T]()`, `@min_int[T]()`, and `@max_int[T]()` answer
  as constants.
- The prelude arrives: `none`, `true`, `false`, `bool`, and `str`.
- `std.mem` opens the standard library with `align_up` and `eql`.
- `std.debug.assert` arrives over `@trap()`, and `std.math` opens with
  `is_power_of_two`.
- A union may stand in a bracket, so `Box[u32 | none]` means the union it spells.
- What a call feeds may pin its type argument.
- A struct literal may leave out the type where what it lands on says it.
- A literal folds where its parts are constant.
- `==` and `!=` compare two pointers by address.
- Reaching a member by the wrong kind is refused.
- A `var` no longer asks a sealed constant for the type it already carries.

### Compiler

- A shift is bounded by the width it shifts.
- A `break` carrying a value that never arrives leaves its loop's type to the
  arms that do.
- `E0248` retires.

## [0.2.0] - 2026-08-08

The language is now Phi, and it is redesigned around one idea: a type may be
several types, and a branch that settles which one narrows the value to it.

### Language

- `type Timeout` declares a unit type.
- `A | B` is a union type, its members distinct and ordered.
- A value enters a union by membership, and comes back out through a branch.
- A condition is a union asking whether it holds its first member.
- `e is T` tests which member a union holds and narrows the tested name.
- `e or f` is the first member of `e`, or else `f`.
- `match` splits a union into one arm per member, exhaustive by counting.
- `bool` left the compiler: `type bool = true | false` is an ordinary
  declaration.
- An alias may be generic, `type Maybe[T] = T | none`.
- An annotation seals a constant.
- Gone: optionals `?T`, error unions `!T`, `error Name`, `try`, `catch`,
  `orelse`, `null`, and the `|v|` capture.
- `loop` replaces `while`.
- `type X = { }` replaces `struct X { }`.
- A struct literal names the type it builds, `Point.{ x: 1 }`.
- `use` is now `import`, and prefix `!` is now `not`.
- New operators: `&`, `|`, `^`, `~`, `<<`, `>>`, compound assignment, `p.*`,
  and `a[i]`.
- `intrinsic` is a keyword only the standard library reaches.
- A method without `pub` is private to its file.

### Compiler

- A parse error stops nothing: the parser reads the whole file.
- Function bodies check from a flat worklist, so a call chain of any depth
  compiles.
- Output is deterministic.
- Number literals are validated exactly.
- Edges that crashed now report.
- `E0216`, `E0217`, and `E0224` through `E0229` retire.

### Command line

- Both commands close with `checked in 1.234ms` on standard error.

### Distribution

- Every commit on `main` that passes CI is published as a dev build at the `dev`
  tag, with an `index.json` naming the version, the commit, and every checksum.

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

[Unreleased]: https://github.com/arshad-yaseen/phi/compare/0.4.0...HEAD
[0.4.0]: https://github.com/arshad-yaseen/phi/compare/0.3.0...0.4.0
[0.3.0]: https://github.com/arshad-yaseen/phi/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/arshad-yaseen/phi/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/arshad-yaseen/phi/releases/tag/0.1.0

# Changelog

## [Unreleased]

### Language

- A field without `pub` is private to its file, the way a method already is,
  so another file can neither reach it nor build the struct that holds it. A
  struct built elsewhere marks each field `pub`, or has its own file build it
  through a function.
- `@view(p, n)` is a view of `n` elements at a pointer, as writable as the
  pointer, and `@int_from_ptr(p)` is its address as a `u64`. Both are the
  standard library's alone, the way `@ptr_cast` is, because each takes the
  caller's word for what the checker cannot see.
- `@splat` is now `@repeat`, which says what it does without borrowing a word
  from vector code, and leaves `fill` to the function that writes into storage
  something else already owns.
- `std/mem` gains `Arena`, bump allocation over bytes the caller owns:
  `Arena.over(buffer)` makes one, `create[T](value)` and `alloc[T](count,
  value)` hand out one or many, each holding what was given, and `reset` takes
  it all back at once. What does not fit answers `mem.OutOfMemory`.
- `std/mem` gains `fill`, which sets every element of a view to one value.

### Compiler

- A struct holding a unit type, or an array of one, builds to a binary. The
  compiler sized a unit at nothing while the C it wrote gave it a byte, so the
  C compiler refused the disagreement.
- `x or return` with a broken `x` reports `x` alone. It used to take the
  `return` as unconditional and report everything after it as unreachable.

### Command line

- `phi run` retires. A binary is started by its own name, so `phi build` is
  the whole step from source to program, and it closes naming the binary's
  size beside the time.

## [0.4.0] - 2026-08-18

0.3.0 gave a program something to hold. This release runs it: `phi build`
compiles a program through C to a native binary, `phi run` builds and then runs
it, and it starts at `fn main()`. `import` names the modules a file reaches,
`extern fn` reaches past the program itself, and `std/io` writes to standard
output. A generic now asks what its type argument is, with `match T` and
`T is u32`, and a bound holds it to a set of types, so one function covers
every number.

### Language

- An import names a module and nothing else, `import std/math`, where `/`
  separates the names of a path and `.` only ever reaches inside a module. The
  last name binds and `as` renames it, so there are no item imports, no
  aliases for items, and no `pub import`.
- A program starts at `fn main()` in its entry file, a plain function taking
  nothing and returning nothing.
- `extern fn` declares a function the linker finds elsewhere, so a program can
  reach outside itself. Only the standard library writes one, and a signature
  carries numbers and addresses alone, `*T | none` among them, because those
  are what pass unchanged on every target.
- `@splat(v)` is an array whose every element is `v`, taking its type from
  where it lands, so `var buffer: [4096]u8 = @splat(0)` is written once. An
  array of one repeated value is held once however it was written, so its
  length costs nothing to compile.
- A run of lines opening with `\\` is one string, the lines joined by the break
  between them. Each line is raw from the marker to its end, so the indentation
  before it is not part of the text and nothing inside it is an escape.
- A view answers `.ptr` beside `.len`, which is the address it already holds
  and may be written through exactly where the view may.
- `is` and `match` fold where the union is already settled, and a settled
  condition picks its `if` edge before anything runs, so the arm that cannot
  run is never entered, the way a settled `and` never enters its dead side. A
  settled name narrows inside the branch as a running one does, a top-level
  constant among them. Testing a constant optional used to crash the compiler.
- `T is u32` asks whether two types are the same, and `match T` picks the arm
  labeled with the type it is, so a generic specializes on its own type
  argument. Only the chosen arm is checked, and a type no arm names is refused
  where the generic was instantiated.
- A type parameter may be bounded, `fn abs[T: Number](n: T) T`, to the members
  of a type the way a value is held to the members of a union. An argument
  outside the bound is refused where the generic is named, `match T` and `T is`
  count their arms against the bound as a value match counts against its
  union, and a bare number pins the first member of the bound it fits, so
  `abs(-7)` is an `i64`. The prelude declares `Integer`, `Float`, and `Number`
  for it, widest first.
- `is` takes a union on its right, `r is Timeout | NotFound`, and asks for
  any of its members, the way a match arm labeled with several already did.
  The branch narrows to exactly those, and the other to what is left.
- An integer reaches a float the way it reaches a wider integer, with nothing
  written, wherever every value of it is exact: a `u32` is an `f64`, an `i16`
  is an `f32`, and a `u64` is neither. An integer constant that a float would
  round is refused rather than rounded, so `let x: f32 = 16777217` reports
  where it used to lose the one.
- `type X = { }` with nothing inside is refused, because a type with nothing
  inside is `type X`, and one spelling is enough. A struct holding only
  functions stays, since it is a namespace rather than a value.
- A top-level binding takes whatever settles before anything runs, so
  `let size: u64 = @size_of[Node]()` and `let same = Byte is u8` bind where
  they used to be refused. What has to run, such as a call, still cannot.
- A value enters a union through whatever edge its member would have taken on
  its own, so `[]var T` reaches `[]T | none`, a `u32` reaches `u64 | none`, and
  an array literal lands on the member that holds it. Listing one more member
  used to refuse values the member itself took.
- `str` leaves the prelude. Text is bytes, and is written as `[]u8`, so a
  view of bytes has one spelling wherever it appears.
- `std/io` has `print`, which takes text or any integer and writes it to
  standard output, and `format`, which writes an integer's decimal digits into
  a caller's buffer sized by `format_max`. The prelude declares `Signed`,
  `Unsigned`, `Integer`, `Float`, and `Number`, widest first.

### Compiler

- A header that leaves, `if return 1 { }` or `loop i in 0..return 3 { }`,
  lets nothing through, so what follows the construct is reported as
  unreachable the way it is after a bare `return`. A range end that left
  used to crash the compiler.
- The arms of an `if`, a `loop`, or a `match` used as a value name its type
  between them in whichever order they come, so `if c { 1 } else { small }`
  is a `u8` the way `if c { small } else { 1 }` always was. A constant that
  has not landed waits for the arm that has.
- An operator refused on a union says how to narrow it, which only `==` and
  `!=` used to, and only where narrowing could reach a member that takes the
  operator. An operator that mixes a union with a member of it says the same.
- A type parameter written `[]T` is pinned by a literal, since an array that
  has not landed still knows its elements, so `eql("a", "b")` reads `T` as
  `u8`. A hint that is a union pins the member the bound admits and a literal
  fits, so `-7` reaches an `i64` past a `u64` listed before it.
- A report from inside a long chain of instantiations keeps both ends of it,
  the innermost frames and the caller's own, and counts what it leaves out
  between. It used to drop the caller's end, which is the half a reader can
  act on.
- A type standing where a value belongs, `if i64 { }` or `a[[]u8]`, is
  refused, and a compound assignment whose right side is already broken
  reports nothing more. A type as a condition used to pass unreported, a type
  as an index used to crash the compiler, and the assignment added a report
  naming `<broken>`.

### Command line

- `phi build` compiles the program to a native binary for 64-bit targets,
  through C and the system C compiler, and `phi run` builds and then runs it.
  The binary carries debug info naming phi source lines, `--opt fast|small`
  says which the C compiler favours, and neither setting changes what a
  program means.

## [0.3.0] - 2026-08-11

Unions gave 0.2.0 its shape. This release gives a program something to hold:
`[N]T` lays values end to end, `[]T` views values it does not own, `a[x..y]` is
the one bridge between them, and text is bytes that fit either. Every type now
answers its size and alignment, so what a value costs is settled before
anything runs. A standard library opens on top of that, over a prelude that
gives `none`, `bool`, and `str` one meaning in every file.

### Language

- `[N]T` is an array, N values of one type laid out end to end and written
  `[1, 2, 3]`. The length lives in the type, so it costs no memory and answers
  as `a.len`, `a[i]` is a place the way a field is, and an index past the end is
  refused before anything runs or checked before the memory is touched.
- `[]T` is a view of elements it does not own, two words wide, and `[]var T`
  also writes through and fits wherever a `[]T` is asked. It holds no elements,
  so a type may hold a view of itself, and `[]T | none` costs no more than the
  view alone.
- `a[x..y]` is the single bridge from storage to a view, spelled as an
  expression so a reader sees the moment it happens. `a..` runs to the base's
  own length, what the view may write is what the place it came from allowed,
  and a range that leaves its base is refused before anything runs or checked
  before the view is made.
- A constant that lands on a view gets bytes the program owns, so `[2, 3, 5, 7]`
  fits a `[]u32` and one written twice is one set of bytes. It never fits a
  `[]var T`, and an array with a part settled at run time is refused rather
  than viewed from a frame that is about to leave.
- A string is bytes and a character is a number, both written as constants that
  fit where their values fit: `"text/plain"` returned as `[]u8` is bytes the
  program owns, `let magic: [2]u8 = "hi"` is storage with its length checked,
  and `s[i] == 'a'` compares two numbers. Escapes decode at compile time, and a
  literal never crosses a line.
- `loop i in 0..n` counts a range: the name is a `let` for the pass, both ends
  are read once before the first, and the counter takes the type of the ends,
  `u64` where neither says. `in` joins the keywords.
- Every type answers its size and alignment: `bool` is one byte, and
  `*T | none` is one word, with `none` as the zero no valid pointer holds.
  A type past 4 GiB is refused with `E0261`.
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
- `@size_of[T]()`, `@align_of[T]()`, `@min_int[T]()`, and `@max_int[T]()` answer
  as constants that fit wherever their value fits, so `let n: u32 =
  @size_of[Node]()` needs no conversion and `@max_int[u64]()` is exact.
- The prelude arrives: `none`, `true`, `false`, `bool`, and `str` are declared
  once in `std.prelude` and visible in every file, so optionals, truth, and
  text share one identity across modules. A file's own declaration still wins.
- `std.mem` opens the standard library with `align_up`, which rounds an address
  to an alignment it asserts is a power of two, and `eql`, which answers whether
  two views hold the same elements in the same order.
- `std.debug.assert(ok)` arrives over `@trap()`: a violated contract stops the
  program where it stands. `std.math` opens with `is_power_of_two`.
- A union may stand in a bracket, so `Box[u32 | none]` means the union it
  spells.
- What a call feeds may pin its type argument: in `let a: u64 =
  mem.align_up(11, 8)` the annotation decides `T` where the arguments leave it
  open, and the return type reads the same way, so an annotation reaches a type
  argument no parameter mentions. An argument pins through whatever its
  parameter is written in, `T`, `*T`, `[]T`, and `[N]T` alike, and a width
  stated nowhere still refuses.
- A struct literal may leave out the type where what it lands on says it, so
  `let p: Point = .{ x: 1, y: 2 }` reads once instead of twice, as do an
  argument, a return, a field, and an element. It still names the type where
  nothing lands it, and where what lands it is a union.
- A literal folds where its parts are constant, whether it builds an array or a
  struct, so `Point.{ x: 1, y: 2 }` binds at the top level, sits inside an
  array, and costs no instruction, while one with a runtime part is built where
  it stands.
- `==` and `!=` compare two pointers by the address each one is, and what may be
  written through a pointer is not part of that. Everything they still refuse
  says what answers instead: `is` for a union, `std.mem.eql` for a view, a
  written comparison for a struct.
- Reaching a member by the wrong kind is refused: calling a field used to
  compile silently, reading a method now says to call it, and a missed name
  suggests methods as well as fields.
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

[Unreleased]: https://github.com/arshad-yaseen/phi/compare/0.4.0...HEAD
[0.4.0]: https://github.com/arshad-yaseen/phi/compare/0.3.0...0.4.0
[0.3.0]: https://github.com/arshad-yaseen/phi/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/arshad-yaseen/phi/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/arshad-yaseen/phi/releases/tag/0.1.0

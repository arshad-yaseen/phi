# Roadmap

What Phi does next, and why in this order.

One rule decides the sequence. **A claim the compiler cannot demonstrate is a
claim nobody can check.** The language exists to prove memory safety from the
allocator a program was already passing down, and today it proves nothing at
all, because nothing runs. Every phase below either makes a claim provable or
makes the next phase possible.

## The chain that is forced

Most of the order is a dependency, not a preference:

```
a backend  ->  extern fn  ->  Arena  ->  the region checker
```

`Arena.create[T]()` hands back a pointer to memory it got from somewhere. There
is no somewhere. Memory has to come from `mmap` or `malloc`, which means calling
C, which means declaring a foreign function, which means something has to emit
code for the call. So the memory model, the thing the language is named for,
sits at the end of a chain that starts with running a program.

Everything outside that chain is a judgment call, and is marked as one.

## 0. Cut 0.3.0

`## [Unreleased]` holds twenty three entries someone could act on, and
`build.zig.zon` already says `0.3.0`. By the trigger in `CLAUDE.md` the release
is due. Cut it before the next phase starts, so the work below lands against a
numbered baseline rather than on top of a backlog.

## 1. Run a program

The single largest gap. `phi check` and `phi ir` are the whole surface, so the
language has never been validated by anything except its own checker. Accepting
the right programs has been tested four hundred and sixty ways. Whether an
accepted program does the right thing has been tested zero ways.

**An entry point.** What `main` is, what it may take, and what its return value
means to the shell. `compile` currently checks every top-level declaration of
the root file, which is right for `phi check` and stays that way. `phi build`
additionally requires an entry and reports its absence.

**`extern fn`.** A declaration with a body somewhere else, named by its C
symbol. This is what makes a backend useful the day it lands, rather than a
month later: `write`, `malloc`, and `mmap` arrive from libc with no ABI work of
our own.

**A C emitter.** The IR is a typed control flow graph over types whose size and
alignment `Layout` already answers, which is close to C already. A C backend
reaches every release target without five code generators, and hands us the
foreign function interface for free. The cost is a C compiler at build time,
which a research language can afford.

Three things in the IR are not C and have to be given meaning here, and each is
a language decision rather than an implementation detail:

- `add`, `sub`, `mul`, and `div` trap rather than wrap. C wraps unsigned and
  invokes undefined behavior on signed, so each becomes a checked helper.
- `bounds_check` and `order_check` are explicit instructions already, and become
  explicit branches.
- `trap` needs to say what stopping looks like: a message, an exit code, or
  both. `std.debug.assert` is the first thing a user will hit it through.

Instance names also need mangling, since `Pair[K, V].swap[T]` is not an
identifier.

**`phi build` and `phi run`.** Emit, invoke the C compiler, and either leave a
binary or run it. `phi check` and `phi ir` keep working as they do.

**`std.io`, one function deep.** `print` over `extern fn write`. Enough to see
that a program ran, which is the entire point of the phase.

**The gaps a real program hits immediately.** These are small and are only
listed here because this is where they start to hurt:

- Walking a view means indexing it by hand, so `loop x in xs` alongside
  `loop i in 0..n`.
- A view indexed inside a loop is bounds checked every pass, even where the
  length was compared three instructions earlier. `std.mem.eql` shows it.

## 2. Test blocks

`test "name" { }` in the file it tests, and `phi test` to run them. This is the
home for standard library tests, which have nowhere to live today: a generic
body is checked only where it is instantiated, so nothing in the suite compiles
`align_up` or `eql` unless something calls them.

It lands here rather than earlier because a test that cannot run is a test that
only re-checks the checker, which `test/` already does better.

## 3. Arena

`std.mem.Arena` over the foreign allocation phase 1 opened. Create it, choose
its backing storage, take a child from it, reset it, destroy it.

Write it as an ordinary library first, with nothing policing it. The region
checker is a separate pass, and giving it a concrete API and real programs to
police beats designing it against an API that does not exist yet.

Its shape is not free, though, so the design document below comes first.

## 4. The memory model

The thesis. `check: remove the memory model` took out a sketch in August with
the reasoning that keeping it would constrain the redesign, and everything since
then, unions, narrowing, arrays, views, text, and layout, has been its
substrate. The removal commit noted that layout did not exist anywhere yet. It
does now.

**Restore the design first.** `memory.md` survives in history at `5cae202`,
five hundred and eighty four lines, and it is a finished model rather than a
sketch. It is written in pre-0.2 Nul, with `struct`, `try`, and `!i64`, so it
needs translating into the union world, not redesigning. It belongs at
`docs/design/memory.md`, a directory `CLAUDE.md` still describes and that no
longer exists.

**Then the checker.** One invariant:

> Every pointer reachable from a value in some arena points into an arena that
> outlives it.

One rejection, storing shorter lived memory into longer lived memory. The check
is local, comparing two arena names already in scope, so it never crosses a
module and never needs whole program analysis. A value carries one arena rather
than one per field, because its tag is a lower bound on everything inside it,
which is also why no region ever appears in a type.

Phase 1 is what makes this provable rather than asserted. A region checker
without execution can only be tested on the programs it refuses, never on
whether the programs it accepts behave.

## Alongside, whenever they are wanted

Neither of these blocks anything, and nothing blocks them.

**`phi fmt`.** Already enabled by a constraint the parser holds today: the tree
is lossless, every token, comment, and position recoverable from it and the
source. Best taken once phase 1 has settled the syntax, since a formatter is the
thing most expensive to redo.

**A language server.** The architecture was built for one. `Compilation` takes a
`Loader` a host replaces with unsaved buffers, `record_expr_types` makes every
expression's type retrievable, and `exprType` answers from data rather than by
re-running anything. Diagnostics and hover are both available now, at the cost
of an LSP shell and nothing else, and the Zed extension already exists to host
them. Completion and go to definition want more of the language to exist first.

## Not on this roadmap

- A native backend. The C emitter reaches every target we ship, and a second
  backend is worth its cost only when the first one is the bottleneck.
- Anything that restricts aliasing. The memory model deliberately does not, and
  gives up per object lifetimes to keep the checker local and the vocabulary
  empty. That trade is the design.
- Package management, build scripts, and incremental caching. The compiler is
  demand driven and memoized per declaration, so incremental compilation is a
  driver away rather than a rewrite, and it is not needed until a program is
  large enough to be slow.

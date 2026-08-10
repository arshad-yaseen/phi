# AGENTS.md

This document defines the coding style and principles that every contribution to this codebase must follow. It is written for human and AI agents alike. Read it once, then keep it close. The rules below are not suggestions.

## Design Goals

Three goals guide every decision, in order of priority:

1. **Safety**
2. **Performance**
3. **Developer experience**

All three matter. Good style advances all three. Style is more than readability. Readability is table stakes, a means rather than an end. Where understanding is missing, style fills the gap.

## Simplicity and Elegance

Simplicity is not a concession to the other goals. It is the "super idea" that solves multiple constraints simultaneously to achieve elegance.

Simplicity is not the first attempt but the hardest revision. Spend mental energy upfront, proactively. An hour of design saves weeks in production.

> "Simplicity and elegance are unpopular because they require hard work and discipline to achieve." Edsger Dijkstra

## Zero Technical Debt

Do it right the first time. The second time may never come, and steady incremental progress depends on knowing that what shipped is solid.

Do not allow potential latency spikes, exponential-complexity algorithms, or other showstoppers to slip through. When a problem is discovered, solve it. Do not defer.

## Answers, Not Passes

There is one engine and many hosts. A batch check, an editor answering
keystroke by keystroke, an incremental rebuild after an edit, and a parallel
sweep across cores are the same code running the same units on different
schedules. None of them is a mode, and retrofitting any of them into a
pass-ordered compiler is a rewrite, so one rule judges every change now:

**Every semantic question is a bounded, memoized unit of work, and a unit may
depend on other units' finished answers, never on how, when, where, or in
what order anything ran.**

The rest is that rule meeting the code. Units compute on demand, so nothing
is computed unasked and nothing twice, which is where the speed comes from.
No unit reads another's half-built state, which is what leaves a schedule
free to reorder, thread, or replay them. A caller consumes a callee's
signature, never its body, so an edit inside a body invalidates that body
alone. Outputs, whether diagnostics, types, or IR, are attributable to the
unit that produced them, so re-running one replaces exactly its own work.
The type of an expression is data the checker produces, so lowering is one
consumer of the answer rather than the only place it exists, and the tree is
lossless, every token, comment, and position recoverable from it plus its
source.
Identity is a declaration, a node, or an interned index, never a byte offset
that shifts under every keystroke, and long-lived tables are append-only, so
a new generation can stack over an old one. Rendered output is canonical,
file order for diagnostics and instance order for IR, so no schedule can
show through it. Sources arrive through one loading seam a host can replace
with unsaved buffers, and I/O reaches no deeper. And broken input is the
common case: parsing always yields a whole tree, analysis poisons locally
and keeps answering, and a budget may stop reporting, never analyzing.

The test for any change is one question. Would the answer differ if units ran
in another order, on another thread, or against an edited buffer? If it
could, it is a bug today, whether or not the current driver can reach it.

## Safety

### Control Flow

- Use only very simple, explicit control flow. Avoid recursion where iteration suffices; when recursion is unavoidable, give it a bounded depth and assert that bound. Bounded execution must be guaranteed.
- Use only a minimum of excellent abstractions, and only when they make the best sense of the domain. Abstractions are never zero cost, and every abstraction introduces the risk of leaking.
- **Put a limit on everything.** All loops and all queues must have a fixed upper bound to prevent infinite loops or tail-latency spikes. Where a loop cannot terminate (e.g. an event loop), assert this.
- **A limit is invisible or diagnosed, never silent.** Every bound is one of two
  kinds. An engineering bound guards an implementation choice that no input can
  reach. Pick it generously and assert it at the boundary. A language limit can
  be reached by a written program, so it is a design decision. It gets a
  diagnostic code, and crossing it reports an error that names the limit. What
  no bound may do is silently change what a program means. A cap that quietly
  degrades behavior when reached is a bug wearing a limit's uniform.
- Use explicitly-sized integer types like `u32`. Avoid architecture-specific types like `usize`. The one accepted exception is the seam with the Zig standard library: `std.ArrayList.len`, slice indices into `[]const u8`, and similar interop are typed `usize` by the language. Keep `u32` everywhere we own the type, and limit `usize` to those boundaries (no `@intCast` chains that just propagate the boundary outward).

### Assertions

Assertions detect programmer errors. Unlike operating errors, which are expected and must be handled, assertion failures are unexpected, and crashing is the only correct response. Assertions downgrade catastrophic correctness bugs into liveness bugs. They are a force multiplier for fuzzing.

- **Assert all function arguments, return values, pre/postconditions, and invariants.** A function must not operate blindly on data it has not checked. Assertion density must average at least **two assertions per function**.
- **Pair assertions.** For every property to enforce, find at least two different code paths where an assertion can be added. For example, assert the validity of a node's shape immediately before serializing it, *and* immediately after deserializing it back.
- A blatantly true assertion can be used in place of a comment when the condition is critical and surprising. It is stronger documentation.
- **Split compound assertions:** prefer `assert(a); assert(b);` over `assert(a and b);`. The former reads simpler and gives more precise failure information.
- Use single-line `if` to assert an implication: `if (a) assert(b);`.
- **Assert relationships between compile-time constants.** Compile-time assertions check design integrity *before* the program executes. They are extremely powerful.
- **The golden rule:** assert the **positive space** (what you expect) AND the **negative space** (what you do not expect). The boundary between valid and invalid is where interesting bugs live. Tests must cover both spaces exhaustively, including the transition from valid to invalid.
- Assertions are a safety net, not a substitute for understanding. A fuzzer proves only the presence of bugs, never their absence. Therefore:
  - Build a precise mental model of the code first.
  - Encode that understanding as assertions.
  - Write the code and comments to explain and justify the model to your reviewer.
  - Use fuzzing as the *final* line of defense.

### Memory

- **Allocate with intent, not by reflex.** Prefer arena allocators with a well-defined lifetime over per-object alloc/free. An arena makes the allocation pattern visible at the call site, eliminates use-after-free, and frees in one step.
- **Reserve before you fill. Always, and an estimate is enough.** Any time a
  collection's final size is known, bounded, or merely *estimable*, reserve it
  once up front. Do not wait for certainty: being wrong costs a single
  reallocation, while not guessing costs a copy of the entire buffer at every
  doubling. Derive the estimate from whatever input drives the size and say so in
  a comment.

  ```zig
  // one node per eight source bytes, measured against real files
  try nodes.ensureTotalCapacity(gpa, source.len / 8 + 8);
  ```

  Reserving earns its keep on its own, whether or not the writes that follow can
  use the `...AssumeCapacity` variants. The reservation is what removes the
  reallocations and the copies; assume-capacity removes a per-item branch on top
  of that. Do the first even when you cannot do the second.

- **Then commit with `...AssumeCapacity`.** Once capacity is reserved, use the
  assume-capacity variants for the writes that follow. The reservation becomes the
  single place that can fail, so the loop body has no error path, no capacity
  check, and no chance of moving the buffer under a live pointer.

  ```zig
  try nodes.ensureUnusedCapacity(gpa, fields.len);
  for (fields) |field| nodes.appendAssumeCapacity(field); // cannot fail, cannot move
  ```

- **Never construct a container inside a loop.** A list created, filled, and
  freed per iteration pays an allocation, a run of reallocations, and a free every
  single time around, and throws away the capacity it just earned. Hoist it out of
  the loop. Better still, put it on the parent struct. Clear it per iteration so
  the capacity earned by the first pass serves every pass after.

- **One scratch buffer, marked and restored.** When work nests or recurses, do not
  give each level its own buffer. Keep one on the parent, record its length on
  entry, and truncate back to that mark on the way out. Every level gets the tail
  it needs, all of them share one capacity, and the whole traversal costs one
  allocation.

  ```zig
  const top = p.scratch.items.len;
  defer p.scratch.shrinkRetainingCapacity(top);
  ```

- **Keep the capacity, drop the contents.** `clearRetainingCapacity` and
  `shrinkRetainingCapacity` reset the length and keep the buffer.
  `clearAndFree` and `deinit` discard the asset you already paid for. Reach for
  the retaining forms by default; free only when the memory must genuinely go
  back, and say why.
- Long-lived caches and pools must have an explicit upper bound. Unbounded growth is a latency bug waiting to happen.

### Scope and Function Shape

- Declare variables at the **smallest possible scope**. **Minimize the number of variables in scope** to reduce the probability of misuse.
- Good function shape is the inverse of an hourglass: a few parameters, a simple return type, and meaty logic between the braces.
- **Centralize control flow.** Keep `switch`/`if` decisions in the parent and move non-branchy logic to helpers. *Push `if`s up and `for`s down.*
- **Centralize state manipulation.** Let the parent function hold state in local variables and use helpers to compute what should change, rather than mutate directly. Keep leaf functions pure.

### Branches and Conditions

- Compound conditions are hard to verify. Split them into nested `if/else` branches. Split complex `else if` chains into `else { if { } }` trees. This makes branches and cases explicit.
- Consider whether every `if` needs a matching `else` so both positive and negative cases are handled or asserted.
- **State invariants positively.** Negations are not easy. Prefer:

  ```zig
  if (index < length) {
    // The invariant holds.
  } else {
    // The invariant doesn't hold.
  }
  ```

  over the inverted form (`if (index >= length)`).

### Error Handling

- **All errors must be handled.** A majority of catastrophic failures come from incorrect handling of non-fatal errors that were *explicitly* signaled in software. Silently swallowing an error is worse than crashing. Test your error paths.
- Distinguish operating errors (expected, recover and report) from programmer errors (unexpected, assert and crash). Mixing the two confuses callers.
- **Never write `catch unreachable` or `orelse unreachable` to silence an error you have not thought about.** `unreachable` asserts the case cannot happen and must be provable from an invariant you can name. Used as a shortcut it converts a handled failure into a crash in safe builds and undefined behavior in fast ones. When a case truly cannot arise, say why in a comment beside it.
- **`undefined` is a promise to fill.** A variable left `undefined` must be fully written on every path before any read. Where the fill is not immediately adjacent to the declaration, assert the invariant that proves it.

### Motivation and Defaults

- **Always say why.** Every decision should include rationale. Explaining *why* increases the reader's understanding, encourages compliance, and shares criteria for future decisions.
- **Explicitly pass options at the call site** instead of relying on library defaults. Prefer `@prefetch(a, .{ .cache = .data, .rw = .read, .locality = 3 })` over `@prefetch(a, .{})`. This improves readability and prevents latent bugs if the library changes its defaults.

## Performance

> "The lack of back-of-the-envelope performance sketches is the root of all evil."

- **Think about performance from the outset.** The 1000x wins live in the design phase, before you can measure or profile. It is harder to fix performance after implementation, and the gains are smaller. Have mechanical sympathy. Work with the grain.
- **Sketch back-of-the-envelope estimates** for the resources that actually matter to this workload: CPU and memory above all, then disk for reads. Account for both bandwidth and latency. Sketches are cheap. Aim to land within 90% of the global maximum.
- **Optimize the slowest resources first**, but compensate for frequency. A memory cache miss may cost as much as a disk read if it happens many times more.
- **Distinguish the control plane from the data plane.** Configuration, error paths, and one-shot setup are the control plane and can afford to be slow and safe. Per-token, per-node, and per-byte work is the data plane and must be tight. Batching across this boundary delivers high assertion safety without losing performance.
- **Amortize costs by batching** memory, CPU, and I/O access.
- **Let the CPU be a sprinter** doing the 100m. Be predictable. Don't force it to change lanes. Give it large enough chunks of work. This is batching, again.
- **Be explicit. Minimize dependence on the compiler.** Extract hot loops into stand-alone functions with primitive arguments (no `self`). The compiler doesn't need to prove it can cache fields in registers, and a human reader can spot redundant computations more easily.

### Data-Oriented Design

The highest-leverage question in this kind of codebase: **which struct do I have
the most of, and how do I make it smaller?** Tokens, tree nodes, and IR
instructions exist in the millions. A byte removed from one is a byte removed a
million times, and it shows up as cache hits, not as a micro-optimization.

- **Math is cheaper than memory.** A multiply beats an L1 read, and L1 beats L2
  beats L3 beats main memory, each by roughly an order of magnitude. So do not
  memoize what you can recompute: a token's end position, a line and column, a
  canonicalized name. Storing it costs a load on every hot path and bytes in
  every instance forever; recomputing costs a few cycles on the rare path that
  asks.

- **Field order is size.** A struct is not the sum of its fields. `{ u32, u64,
  u32 }` is 24 bytes; the same fields ordered `{ u32, u32, u64 }` are 16. One
  `bool` appended to an 8-aligned struct can cost 8 bytes to carry 1 bit. Order
  fields large to small, and know what a field costs before adding it.

- **Indices, not pointers.** A `u32` index halves a pointer on a 64-bit target
  and drops the struct's alignment from 8 to 4, which often makes the next field
  free. It also survives reallocation, which a pointer does not. The cost is type
  safety. Give each index a distinct enum type such as `Node.Index` or
  `Token.Index`, rather than passing bare integers that can be mixed up.

- **Store booleans out of band.** A flag costs a load and a branch on every
  iteration, and can cost 8 bytes in the struct to carry one bit. Two
  collections, one per state, carry the same information in zero bytes. The pass
  that wants only one state then stops testing entirely.

- **Eliminate padding with struct-of-arrays.** Prefer `MultiArrayList` over
  `ArrayList(Struct)` when a pass walks one field across many rows. Per-element
  padding disappears, and a tag column read on nearly every step stops dragging a
  rarely-read payload through cache beside it. Usually a one-line change.

- **Sparse data belongs in a side table.** If a field is meaningful for a tenth
  of the instances, it does not belong in the struct. Key a map by the index and
  pay for it only where it exists.

- **Encodings beat polymorphism.** When variants need different data, do not size
  every instance for the largest. Give the tag more cases and let a small fixed
  set of general-purpose fields mean different things per case. A tree node
  carries `main_token` plus two payload slots whose meaning the tag decides.
  Choose the encodings from the distribution you actually observe.

- **A stated limit buys a smaller type.** Capping source files at 4 GiB makes
  every offset a `u32` instead of a `u64`. That halves every span in the compiler,
  for a limit no real program notices. Pick the limit deliberately,
  assert it at the boundary, and spend the savings everywhere.

None of this is theoretical. Applying exactly these moves, the Zig compiler took
its token from 64 bytes to 5, its tree node from 120 to 15.6, and its untyped IR
from 54 to 20.3. Those changes alone measured 22% and 39% reductions in wall-clock
time.

### Hot Loops

The data plane is a small amount of code executed an enormous number of times. One cycle saved there is a cycle saved millions of times over. Treat cycles in hot loops as the budget they are:

- **Early-exit before expensive work.** Order checks by `cost × probability`: the cheapest test that rejects the most candidates runs first. A one-cycle compare that skips a function call or a memory load in the common case is the highest-leverage instruction you can write.
- **Make the common case straight-line.** Structure branches so the frequent path falls through without jumping and the rare path jumps away. Branch predictors reward monotony. Move cold paths (errors, rare escapes, slow fallbacks) into separate, out-of-line functions so they stop polluting the instruction cache of the hot path.
- **Replace branch chains with table lookups.** A 256-entry lookup table classifies a byte in one load with zero mispredictions, where an `if`/`else` chain costs a data-dependent branch per arm. Precompute at `comptime` whenever inputs are enumerable.
- **Hoist invariants and cache repeated loads.** Anything the loop does not change (lengths, flags, field loads through pointers) belongs in a local before the loop. Do not make the reader or the compiler re-prove invariance on every iteration.
- **Never allocate in a hot loop.** Allocation is the control plane. Reserve, reuse, or batch before entering the loop.
- **Keep hot data small and dense.** A cache miss costs hundreds of cycles and dwarfs any ALU cleverness. The layout work that earns those hits is above, under Data-Oriented Design; do it before you tune the loop body.
- **Batch validation at the boundary.** Validate once before the loop so the loop body can assume, with an assertion, rather than re-check.
- **Mark cold paths cold.** `@branchHint(.cold)` on an error branch, a report, or a rare escape tells the compiler which side to lay out on the fall-through. Pair it with moving the body into an out-of-line function so the cold code stops competing for instruction cache with the hot code.
- **Don't compute what may never be read.** A line and column table, a formatted message, a canonicalized name: build it the first time something asks, not on the way past. Most diagnostics never fire, so anything phrased eagerly is work thrown away.
- **Measure, then trust the measurement.** Optimize against a stable benchmark: warmed up, repeated, compared by median, run in release mode on a quiet machine. Record the baseline before touching anything, and keep every change that survives only if the numbers say so. Profile to find where the cycles go rather than guessing.

## Developer Experience

> "There are only two hard things in Computer Science: cache invalidation, naming things, and off-by-one errors."

### Naming

- **Get the nouns and verbs just right.** Great names capture what a thing is or does and reveal that you understand the domain. Take time to find names where the whole exceeds the sum of the parts.
- **Do not abbreviate** variable names, except primitive integers used in sorts or matrix calculations. Use long-form flags in scripts (`--force`, not `-f`). Single-letter flags are for interactive use.
- Use proper capitalization for acronyms (`ASTNode`, not `AstNode`; `JSXElement`, not `JsxElement`).
- **Add units or qualifiers** to variable names and put them last, sorted by descending significance. Prefer `latency_ms_max` over `max_latency_ms`. This lines up nicely when `latency_ms_min` is added and groups related variables together.
- **Infuse names with meaning.** `allocator: Allocator` is fine, but `gpa: Allocator` and `arena: Allocator` are excellent: they tell the reader whether `deinit` is needed.
- **Match character lengths for related names.** `source` and `target` align better than `src` and `dest`, and downstream variables like `source_offset` and `target_offset` then line up cleanly in calculations.
- When a function calls a helper, **prefix the helper with the caller's name** to show call history: `parseStatement()` and `parseStatementBody()`.
- **Callbacks go last** in parameter lists. This mirrors control flow, since callbacks are also invoked last.
- **Order matters for readability.** Files are read top-down, so put important things first. `main` goes first. For structs: fields, then types, then methods.

  ```zig
  source: []const u8,
  cursor: u32,

  const Token = struct { tag: TokenTag, span: Span };
  const Lexer = @This(); // This alias concludes the types section.

  pub fn init(gpa: std.mem.Allocator, source: []const u8) !Lexer {
      ...
  }
  ```

  If a nested type is complex, promote it to top-level. When in doubt, sort alphabetically. Big-endian naming helps.

- **Don't overload names** with multiple context-dependent meanings.
- **Think about how names will be used outside the code**, in docs, conversation, derived identifiers. A noun usually beats an adjective or present participle. `parser.scratch` reads cleanly as a section heading, while `parser.parsing` needs rephrasing. Nouns also compose more clearly: `config.statements_max`.
- **Use named arguments** (options structs) when arguments can be mixed up. A function taking two `u64`s must use an options struct. If an argument can be `null`, name it so that `null` is meaningful at the call site.
- Singleton dependencies (allocator, logger) have unique types and should be threaded through constructors *positionally*, from most general to most specific.
- **Say why.** Code alone is not documentation. Comments explain *why*, not *what* (the code already says what). Show your workings only when the next reader would otherwise guess wrong.
- **Don't bloat with comments.** Default to no comment. Only add one when the reason behind the code is genuinely non-obvious: a hidden constraint, a subtle invariant, a workaround for a real bug. If removing the comment wouldn't confuse a future reader, don't write it. Never restate the line below.
- **One line, or none.** A comment is a single line. Needing a second is the signal that it is explaining what the code should say itself, or that a name is wrong, or that the reasoning belongs in a design document or a commit body. Cut until it fits or delete it. The one exception is a drawn block for an encoding or a layout, below, which is a picture rather than prose. Before writing a comment, check whether the declaration's own name and signature already say it, and if they do, say nothing.
- **Comments are timeless, not situational.** Describe the code as it is, never its history or the change that produced it. No `no longer`, `we now`, `was wrong`, `the old way`, `KNOWN GAP`, or one-session narrative. A comment a future reader cannot understand without knowing what the code used to be is dead weight. When behavior changes, update or delete the comment, do not narrate the change.
- **A doc comment is general, the site is specific.** The `///` above a function says what it is for, in a line or less, or nothing where the name already does. Mechanism, cases, and the reasoning behind one line sit on that line, not gathered above the function. A reader skimming signatures gets the what; a reader inside the body meets the why exactly where it applies.
- **Where the code is technical, the comment is technical.** Bits, encodings, and layouts blur in prose. Show the thing itself, concrete values in a small aligned block, laid out the way memory holds them, so the reader sees the mechanism instead of a description of it. One drawn example beats three sentences. This block is the one comment allowed past a single line, it carries one line of prose at most, and the rows have to earn their place the way any other comment does.
- **Internal comments are terse phrases, all lowercase.** No leading capital, no trailing full stop. Keep proper casing only for things that need it (identifier names, proper nouns: `Lexer`, `JSX`, `ECMAScript`). A trailing-line note like `// caller already consumed the `(`` is the target shape, not a multi-sentence paragraph.
- **Public doc comments (`///`) are professional prose.** Proper casing, full sentences, real punctuation. They describe what a name means and how a user is meant to use it. Never leak implementation hand-offs, ticket numbers, TODO chatter, or step-by-step rationale that belongs in the commit message.
- **Tests need a header.** A short comment at the top of a non-trivial test states the goal and methodology so a reader can get up to speed or skip past.
- **No em dashes, semicolons, or colons in comments.** Split into separate sentences instead. They invite run-on prose that obscures the point.

### Cache Invalidation

- **Don't duplicate variables or take aliases** to them. State gets out of sync.
- If a function argument is more than ~16 bytes and shouldn't be copied, pass it as `*const`. This catches bugs where the caller makes an accidental stack copy before the call.
- **Construct large structs in-place** via an *out-pointer* during initialization. This enables pointer stability, allows immovable types, and eliminates intermediate copy-moves that grow the stack.

  In-place initialization is **viral**: if any field is initialized in-place, the container must be too.

  **Prefer:**
  ```zig
  fn init(target: *LargeStruct) !void {
    target.* = .{
      // in-place initialization.
    };
  }

  fn main() !void {
    var target: LargeStruct = undefined;
    try target.init();
  }
  ```

  **Over:**
  ```zig
  fn init() !LargeStruct {
    return LargeStruct {
      // moving the initialized object.
    };
  }

  fn main() !void {
    var target = try LargeStruct.init();
  }
  ```

- **Shrink the scope.** Fewer variables in play means fewer chances to use the wrong one.
- **Calculate or check variables close to where they are used.** Don't introduce variables before they are needed, and don't leave them around after. This avoids POCPOU (place-of-check to place-of-use), a cousin of TOCTOU. Most bugs come from a semantic gap created by distance in time or space.
- **Simpler signatures and return types reduce dimensionality at the call site.** Dimensionality is viral, propagating through the call chain. `void` beats `bool`, `bool` beats `u64`, `u64` beats `?u64`, and `?u64` beats `!u64`.
- **Group resource allocation and deallocation visually** with newlines: blank line before the allocation, blank line after the matching `defer`. Leaks become easier to spot.

### Off-By-One Errors

- The usual suspects are casual interactions between an `index`, a `count`, and a `size`. They are primitive integers but should be treated as distinct types:
  - `index` to `count`: add one (indexes are 0-based, counts are 1-based).
  - `count` to `size`: multiply by the unit.

  This is yet another reason to put units and qualifiers in variable names.

- **Show your intent with division.** Use `@divExact()`, `@divFloor()`, or `div_ceil()` so the reader knows you considered the rounding cases.

### Formatting

- Run the standard formatter, `zig fmt`, over every source.
- **4 spaces of indentation**, not 2. More obvious at a distance.
- **Hard limit: 100 columns per line.** No exceptions. Nothing should hide behind a horizontal scrollbar. Set a column ruler in your editor. To wrap a signature, call, or data structure, add a trailing comma and let the formatter do the rest.

  The motivation is physical: 100 columns lets two copies of the code fit side-by-side on a screen.

- Always brace `if` statements unless they fit on a single line. This is defense in depth against "goto fail;" bugs.

### Dependencies

**Zero dependencies** beyond the language toolchain. Dependencies invite supply-chain attacks, safety risk, performance risk, and slow installs. For foundational code, every cost is amplified throughout the stack above it.

### Tooling

Tools have costs. A small standardized toolbox is simpler to operate than an array of specialized instruments each with its own manual. Invest in your primary toolchain so new problems can be tackled with minimal accidental complexity.

> "The right tool for the job is often the tool you are already using. Adding new tools has a higher cost than many people appreciate." John Carmack

When writing a script, prefer Zig, the codebase's language, over shell. This adds type safety, cross-platform portability, and raises the probability that the script works for everyone, not just those on a particular OS or shell.

Standardization reduces dimensionality as the team grows. Slower in the short term, faster in the long term.

---

These rules will feel like a seat-belt at first, a little uncomfortable. After a while, using them becomes second nature, and not using them becomes unimaginable.

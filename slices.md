# Slices, arrays, and text

Storage, views, and one bridge between them. An array is the data itself,
sized by its type. A slice is a two-word view of someone else's data,
sized at runtime. Slicing is the one way an array becomes a slice, spelled
as an expression, never as a coercion. Growth belongs to the library: the
language ships no `cap`, no `append`, and no owner type, because a view
that secretly owns is the trap every neighbor documented.

Text follows from the same pieces. A string is bytes, a string literal is
an untyped constant that fits where bytes are asked, and a character
literal is an untyped integer whose value is the codepoint. The compiler
carries no string type and no character type: `str` is one alias in the
prelude, and everything character-shaped is the fit-by-value rule the
constants already obey.

## Arrays

`[N]T` is N values, contiguous, and nothing else. The length lives in the
type, so it costs no memory and is known at compile time. The size is
N times the stride, the element size rounded to its alignment, so
`arr[i]` is `base + i * stride` and every element lands aligned.

```phi
var arr: [4]u32 = [10, 20, 30, 40]

// offset   0       4       8       12
//        [  10  ][  20  ][  30  ][  40  ]    sixteen bytes, that is all
```

An array is a value. Assigning one copies its bytes, a parameter of array
type is a copy, and an array field sits inline in its struct, the way a
`u64` field does. `arr.len` answers the length as a folded constant, and
an index that is itself a constant is checked at compile time: `arr[9]`
on a `[4]u32` is refused before anything runs.

```phi
type Header = {
    magic: [4]u8        // inline, four bytes, no pointer
    version: u32
}
```

An array literal spells its elements and is an untyped constant, the
rule numbers and strings follow. It knows its own length, so no length
is ever inferred, marked, or counted by hand: unannotated it stays
untyped and adapts at use, it fits `[N]T` with the count checked, and it
fits `[]T` as a read view of constant data, where no length is written
at all.

```phi
let table = [2, 3, 5, 7]        // untyped, adapts where it lands
fn scan(xs: []u32) { }

scan(table)                     // a read view, nothing counted
let held: [4]u32 = table        // storage states its count, checked
```

## Slices

`[]T` is a pointer and a length, two words. It holds no elements, it
views someone else's, and the mutability position mirrors pointers:
`[]T` reads, `[]var T` also writes, and a `[]var T` fits wherever a
`[]T` is asked, the same one subtyping edge pointers have.

```phi
let s = arr[1..3]

// arr:  [  10  ][  20  ][  30  ][  40  ]
//                ↑
// s:    { ptr ───┘, len = 2 }        one address, one count
```

The length lives in memory because a slice can view any portion of
anything: the length is data, not type. `s.len` reads it as a `u64`. The
pointer is not reachable, so the representation stays the compiler's, the
same rule the union tag follows, and the pointer is never null, so
`[]T | none` packs `none` into the pointer word's zero and an optional
slice costs nothing.

Slices alias. Copying a slice copies the view, two words, never the
elements, and two views of one array see each other's writes:

```phi
var arr: [4]u32 = [10, 20, 30, 40]
let s = arr[0..]

arr[1] = 99
// s[1] == 99, the same bytes through another name
```

Emptiness and absence are different questions with different answers.
Empty is `s.len == 0`, a slice viewing nothing. Absent is `[]u8 | none`,
a union, handled by a branch. Nothing conflates them, and an empty
slice's pointer stays non-null so the niche always holds.

## Slicing, and ranges

Slicing takes a view: `arr[a..b]` is `ptr = base + a * stride` and
`len = b - a`, pointer arithmetic and nothing more, the same cost for
four elements as for four million. `arr[a..]` runs to the end. Slicing a
slice views the same underlying bytes.

```phi
fn sum(xs: []u32) u32 {
    var total: u32 = 0
    loop i in 0..xs.len {
        total += xs[i]
    }
    return total
}

fn drive() u32 {
    var arr: [4]u32 = [10, 20, 30, 40]
    return sum(arr[0..])                // the one bridge, written out
}
```

Mutability follows the place: slicing a `var` array yields `[]var T`,
slicing a `let` or a parameter yields `[]T`, and slicing through a
pointer follows the pointer's own mutability, the rules assignment
already obeys.

A range is syntax, not a value. `a..b` exists inside a bracket and in a
loop header, excludes `b`, and there is no range type, nothing to name,
store, or iterate twice. `a..` exists only in a bracket, where the end
is the length.

## Bounds

An index is checked against the length where the memory is touched. A
constant index into an array is refused at compile time. A runtime index
traps in safe builds, by the rule that what the compiler inserted may
vanish in a fast build. These are the checks the memory-safety work
discharges with proofs where it can, so arithmetic wrongness upstream
cannot become a write to memory the program does not own.

## Strings

A string is bytes. A string literal is an untyped constant, the third
sibling of the untyped integer and float, and fits where bytes are
asked, by construction rather than conversion:

```phi
let name = "arshad"                  // an untyped string constant
fn greet(name: []u8) { }             // "arshad" fits
let magic: [2]u8 = "hi"              // fits the array too, length checked
```

A literal fits `[]u8` and never `[]var u8`: constant data is read-only,
and the view's own mutability is what enforces it, so read views share
safely by construction.

The prelude names the convention in one line, and an alias is not a new
type, so there is nothing to convert between:

```phi
pub type str = []u8
```

Escapes decode at compile time: `\n`, `\t`, `\\`, `\"`, `\x41` for a
byte, `\u{1F980}` for a codepoint's UTF-8 bytes. A literal is UTF-8
because source files are, and that is a convention, not a type
invariant. The bytes of `"héllo"`:

```
//   h     é          l     l     o
//  0x68  0xC3 0xA9  0x6C  0x6C  0x6F      six bytes, five characters
```

`s.len` is six, honestly, and `s[1]` is `0xC3`, honestly, half of `é`.
Where character-level meaning matters, it is a boundary function whose
fallibility is spelled in its signature, the one mechanism where a
validity invariant breeds a second slice universe:

```phi
// std.unicode
type InvalidUtf8
type Decoded = { codepoint: u32, width: u64 }

pub fn decode(s: []u8) Decoded | InvalidUtf8
```

## Characters

A character literal is an untyped integer whose value is the Unicode
scalar. It fits by value, the rule every untyped constant follows, and
that one rule answers the whole width question:

```phi
let a = 'a'                          // untyped 97
if s[i] == 'a' { }                   // compares with a byte, no cast

let crab: u32 = '🦀'                 // untyped 129408, fits u32
let bad: u8 = '🦀'                   // refused, 129408 does not fit u8
```

There is no character type and nothing pretending to be one. A program
that wants nominal distinctness declares it, the cost every distinct
type pays:

```phi
type Codepoint = { value: u32 }
```

## loop in

`loop x in e` walks a sequence. Over a slice it binds each element as a
place, mutable exactly when the slice is `[]var T`. Over a range it
binds each integer. Over anything else it calls `e.next()`, which
returns `T | none`, so a type is iterable by having that one method,
with no protocol to declare:

```phi
loop x in xs { total += x }          // a slice, x is the element
loop i in 0..n { }                   // a range, i counts
loop job in queue { run(job) }       // queue.next() until none

loop b in bytes {
    if b == ' ' { break }
}
```

Labels, `break`, `continue`, values, and `else` compose as on every
loop. The header still never narrows, and `or break` in the body does
the same work with a name.

## Equality, and where the library begins

`==` stays numeric. On a fat pointer it is ambiguous, the same view or
the same contents, the ambiguity a generation of languages shipped as
bugs, so contents are asked by name:

```phi
// std.mem
pub fn eql[T](a: []T, b: []T) bool {
    if a.len != b.len { return false }

    loop i in 0..a.len {
        if a[i] != b[i] { return false }
    }
    return true
}
```

One length compare rejects most mismatches in one instruction, and the
element loop is the C compiler's to vectorize.

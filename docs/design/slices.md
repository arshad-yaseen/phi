# Slices, arrays, and text

Storage, views, and one bridge between them. An array is the data
itself, sized by its type. A slice is a two-word view of data it does
not own, sized at runtime. Slicing is the one way an array becomes a
slice, spelled as an expression, never as a coercion, because a view
that secretly owns is the trap every neighbor documented.

Text is not a fourth thing. A string is bytes and a character is a
number, both spelled as constants that fit where they land. The compiler
carries no string type and no character type.

Three rules carry all of it, and each is a rule the language already
needed:

- A name after a dot is a **member**, asked the same way of every type.
- A literal is an **untyped constant**, placed by the one fitting rule.
- An index yields a **place**, the same as a field does.

## Members, one question

A name after a dot asks one question, and every type answers it the same
way: what does this name mean here. A struct answers from its
declaration. An array and a view answer `len`. One question, one answer
per type, no second mechanism.

```phi
point.x                                 // a field, from the declaration
point.norm()                            // a method, from the declaration
arr.len                                 // a member, from the type
```

`len` is not a keyword and not reserved. A struct may declare a field
called `len`, and there it is the field, because nearer declarations win
over further ones the way they do everywhere else.

A member answers at compile time where it can. An array's length is in
its type, so it is settled before anything runs and may size another
array. A view's length is data, so it is read. Either way it reads as
`u64`, because folding is about *when* a value is known and never about
what type it is.

```phi
let arr: [4]u32 = [10, 20, 30, 40]
let copy: [arr.len]u32 = arr            // a length, known and reusable
```

Refused: `len` as a reserved word, which takes a good field name from
every program to save the compiler one lookup. A builtin member reached
by a rule of its own, which is how a language grows a table of
exceptions no reader can find. A length whose type follows the thing
measured, which makes every comparison a question.

## Constants, one family

A literal that has not met a type yet is an untyped constant, and one
rule places every one of them: it fits where its value fits.

```phi
let count = 42                          // an untyped number
let ratio = 1.5                         // an untyped float
let letter = 'a'                        // an untyped number, 97
let name = "arshad"                     // untyped bytes
let table = [2, 3, 5, 7]                // an untyped array
```

Each adapts to the type it meets and is refused when it cannot fit,
whatever its shape:

```phi
let small: u8 = 200                     // fits
let big: u8 = 300                       // refused, does not fit
let crab: u32 = '🦀'                    // fits, 129408
let four: [4]u32 = [1, 2, 3, 4]         // fits, the count checked
let three: [3]u32 = [1, 2, 3, 4]        // refused, four elements
let magic: [2]u8 = "hi"                 // fits storage, length checked
```

An annotation seals a constant, and the sealed type travels with it. An
untyped constant that meets no type is refused where it is bound,
because a binding must know what it holds.

```phi
let sealed: u64 = 2                     // a u64 everywhere it goes
var loose = 5                           // refused, nothing says the type
```

This is what keeps text from needing types of its own. A character
literal is a number, so comparing it to a byte compares two numbers. A
string literal is bytes, so passing it where bytes are asked is not a
conversion.

Refused: per-literal-kind fitting rules, which multiply the one thing a
reader must learn by the number of ways to write a value.

## Arrays

`[N]T` is N values, contiguous, and nothing else. The length lives in
the type, so it costs no memory and is known at compile time. The size
is N times the stride, the element size rounded to its alignment, so
`arr[i]` is `base + i * stride` and every element lands aligned.

```phi
var arr: [4]u32 = [10, 20, 30, 40]

// offset   0       4       8       12
//        [  10  ][  20  ][  30  ][  40  ]    sixteen bytes, that is all
```

An array is a value. Assigning one copies its bytes, a parameter of
array type is a copy, and an array field sits inline in its struct the
way a `u64` field does. Arrays nest, and nesting only multiplies.

```phi
type Header = {
    magic: [4]u8                        // inline, four bytes, no pointer
    version: u32
}

let grid: [2][3]u8 = [[1, 2, 3], [4, 5, 6]]     // six bytes
```

An array literal states its own length, so no length is ever inferred,
marked, or counted by hand.

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

The length lives in memory because a view may cover any portion of
anything: it is data, not type. The pointer is not reachable, so the
representation stays the compiler's, the rule the union tag follows, and
it is never null, so `[]T | none` packs `none` into the pointer word's
zero and an optional view costs nothing.

Views alias. Copying one copies the view, two words, never the elements,
and two views of one array see each other's writes.

```phi
var arr: [4]u32 = [10, 20, 30, 40]
let s = arr[0..]

arr[1] = 99
// s[1] == 99, the same bytes through another name
```

Empty and absent are different questions. Empty is `s.len == 0`, a view
covering nothing. Absent is `[]u8 | none`, a union, settled by a branch.
An empty view's pointer stays non-null, so the niche always holds.

Refused: a view that may own, the trap this design exists to avoid. A
reachable pointer field, which locks the representation into the ABI on
the first day. `null` as an empty view, which answers two questions with
one value and gets both wrong.

## Where a view comes from

`arr[a..b]` is the ordinary way and the only way a program writes. The
standard library reaches one more, because a block that came from the
operating system is not yet anything a program can slice, and everything
that grows begins there:

```phi
// std.mem, where the unsafe seam is named and confined
pub fn view_of[T](at: *var T, count: u64) []var T
```

That one function is the whole of what growth needs from the language.
Above it, a growable buffer is an ordinary struct holding a view and a
capacity, written in the language and readable by anyone:

```phi
type List[T] = {
    items: []var T                      // what is live
    capacity: u64                       // what is owned
}
```

The seam stays a seam. It sits where every unsafe primitive sits, a
program that never writes an allocator never meets it, and no view
anywhere gives its pointer back.

A constant is the third source. A number is a value and needs no address
to exist, but a view *is* an address, so a constant that lands where a
view is asked for needs bytes something can point at. Those bytes belong
to the program rather than to a call, live as long as it runs, and are
shared by every mention of the same constant, which is what makes
handing one back sound:

```phi
fn kind() []u8 {
    return "text/plain"                 // outlives the call, by construction
}
```

Nothing here is particular to text. `[2, 3, 5, 7]` landing on a `[]u32`
is the same constant meeting the same rule, and a literal that lands on
`[N]u8` instead is copied into that storage and needs no address at all.
The rule is not about what was written but about what it became.

Refused: a constant view borrowed from the frame that mentioned it,
which is a dangling view the moment it is returned, and which copies the
same bytes at every mention besides.

## Slicing, and ranges

Slicing takes a view: `arr[a..b]` is `ptr = base + a * stride` and
`len = b - a`, pointer arithmetic and nothing more, the same cost for
four elements as for four million. Slicing a view covers the same bytes.

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
slicing a `let` or a parameter yields `[]T`, slicing a temporary yields
`[]T` because no one else can see it, and slicing through a pointer
follows the pointer's own mutability. These are the rules assignment
already obeys, and slicing invents none of its own.

A range is syntax, not a value. `a..b` excludes `b`, and there is no
range type, nothing to name, store, or iterate twice. A range takes the
type of its ends, the way arithmetic does, so ends that disagree are the
error mixed arithmetic already is.

`a..` leaves the end to the base, so it asks the base for a length. An
array and a view both answer. A base that does not know its own length
has no end to run to, and the open form is refused on it rather than
guessed at. The rule belongs to the base, not to the syntax, so anything
that later knows a length inherits it and anything that does not is
already answered.

Refused: an implicit array-to-view edge, which hides the one moment a
reader needs to see. An inclusive `a..=b` beside the exclusive form, two
spellings whose difference is one character and a bug. A range as a
value, which wants a type, iteration, and a library of its own to answer
questions no program asked.

## Indexing, and bounds

`a[i]` names a place, exactly as `p.field` does, so everything that
composes with a field composes with an element: reading it, assigning
it, taking its address, and reaching through it.

```phi
var grid: [2][3]u32 = [[1, 2, 3], [4, 5, 6]]

let cell = grid[1][2]                   // read
grid[1][2] = 7                          // write
let at = &grid[0][0]                    // address
```

An index is a count, so any integer indexes. That is the operator's
domain, the way arithmetic's domain is numbers, and no value changes
type on the way in.

An index is checked against the length where the memory is touched. A
constant index into an array is refused at compile time, because the
answer is already known. A runtime index traps in safe builds, by the
rule that what the compiler inserted may vanish in a fast build.

```phi
let arr: [4]u32 = [10, 20, 30, 40]
let bad = arr[9]                        // refused, before anything runs
```

## Text

A string is bytes. A string literal fits where bytes are asked, by
construction rather than conversion, and a character literal is the
codepoint's number.

```phi
fn greet(who: []u8) { }

greet("arshad")                         // fits a view
let magic: [2]u8 = "hi"                 // fits storage, length checked
if s[i] == 'a' { }                      // compares two numbers, no cast
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
Where character meaning matters it is a boundary function whose
fallibility is spelled in its signature, the one place a validity
invariant would otherwise breed a second view universe:

```phi
// std.unicode
type InvalidUtf8
type Decoded = { codepoint: u32, width: u64 }

pub fn decode(s: []u8) Decoded | InvalidUtf8
```

A program wanting nominal distinctness declares it, the cost every
distinct type pays:

```phi
type Codepoint = { value: u32 }
```

Refused: a string type carrying a UTF-8 invariant, which makes every
byte view a conversion and every conversion a check. A character type,
which needs conversions to and from the integers it already is. A null
terminator in the language, which is a calling convention and belongs in
the function that calls out.

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

The line is drawn once and holds. The language gives storage, views, the
bridge between them, and the three rules above. Everything that grows,
searches, sorts, allocates, formats, or decodes is a function with a
signature, written in the language, refusable by reading it.

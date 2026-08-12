# Phi

**A systems programming language that proves memory safety at compile time, with no runtime and nothing to annotate.**

> How much of memory safety can be proven from the allocator you were already passing down, without a borrow checker to learn?

A research project.

```zig
import std.io

type BadDigit = {
    at: u64
}

fn parse(text: str) u64 | BadDigit {
    var value: u64 = 0
    loop i in 0..text.len {
        let digit = text[i]
        if digit < '0' or digit > '9' {
            return BadDigit.{ at: i }
        }
        value = value * 10 + (digit - '0')
    }
    return value
}

fn check(text: str) {
    let value = parse(text) or bad {
        point(text, bad.at)
        return
    }
    if value == 42 {
        io.print("Hello, world!\n")
    }
}

fn point(text: str, at: u64) {
    io.print(text)
    io.print("\n")
    var margin: [64]u8 = @splat(' ')
    margin[at] = '^'
    io.print(margin[0..at + 1])
    io.print("\n")
}

fn main() {
    check("42")
    check("4x2")
}
```

```console
$ phi run main.phi
Hello, world!
4x2
 ^
```

## Builds

Builds for macOS, Linux, and Windows are on the [releases page][releases].

[releases]: https://github.com/arshad-yaseen/phi/releases

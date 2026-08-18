# Phi

**A systems programming language that proves memory safety at compile time, with no runtime and nothing to annotate.**

> How much of memory safety can be proven from the allocator you were already passing down, without a borrow checker to learn?

A research project.

```zig
import std/io

fn main() {
    io.print("Hello, world!\n")
}
```

```console
$ phi run main.phi
Hello, world!
```

## Builds

Builds for macOS, Linux, and Windows are on the [releases page][releases].

[releases]: https://github.com/arshad-yaseen/phi/releases

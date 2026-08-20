const std = @import("std");
const builtin = @import("builtin");

os: Os,
arch: Arch,

const Target = @This();

/// The tag names are the spelling `@target_os` looks for, so `std/target` names
/// its unit types after them and the two cannot drift.
pub const Os = enum { linux, macos, windows };

pub const Arch = enum { x86_64, aarch64 };

/// What build targets.
pub const host: Target = .{
    .os = switch (builtin.target.os.tag) {
        .linux => .linux,
        .macos => .macos,
        .windows => .windows,
        else => @compileError("phi has no name for this host operating system yet"),
    },
    .arch = switch (builtin.target.cpu.arch) {
        .x86_64 => .x86_64,
        .aarch64 => .aarch64,
        else => @compileError("phi has no name for this host architecture yet"),
    },
};

pub fn pointerSize(target: Target) u32 {
    const bits = switch (target.arch) {
        inline else => |arch| std.Target.ptrBitWidth_arch_abi(
            @field(std.Target.Cpu.Arch, @tagName(arch)),
            .none,
        ),
    };
    return @divExact(bits, 8);
}

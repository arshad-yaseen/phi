const std = @import("std");
const assert = std.debug.assert;
const builtin = @import("builtin");

pub const Target = enum {
    aarch64_macos,
    x86_64_macos,
    aarch64_linux,
    x86_64_linux,
    aarch64_windows,
    x86_64_windows,
    wasm32_wasi,

    pub const Os = enum { linux, macos, windows, wasi };

    pub const Arch = enum { x86_64, aarch64, wasm32 };

    pub fn os(target: Target) Os {
        return switch (target) {
            .aarch64_macos, .x86_64_macos => .macos,
            .aarch64_linux, .x86_64_linux => .linux,
            .aarch64_windows, .x86_64_windows => .windows,
            .wasm32_wasi => .wasi,
        };
    }

    pub fn arch(target: Target) Arch {
        return switch (target) {
            .x86_64_macos, .x86_64_linux, .x86_64_windows => .x86_64,
            .aarch64_macos, .aarch64_linux, .aarch64_windows => .aarch64,
            .wasm32_wasi => .wasm32,
        };
    }

    pub fn pointerSize(target: Target) u32 {
        // no ABI of our own, and the ones that narrow an address are 32-bit ports
        const bits = switch (target.arch()) {
            inline else => |named| std.Target.ptrBitWidth_arch_abi(
                @field(std.Target.Cpu.Arch, @tagName(named)),
                .none,
            ),
        };
        return @divExact(bits, 8);
    }

    /// Linux takes musl so a program carries its own libc.
    pub fn cTriple(target: Target) []const u8 {
        return switch (target) {
            .aarch64_macos => "aarch64-macos",
            .x86_64_macos => "x86_64-macos",
            .aarch64_linux => "aarch64-linux-musl",
            .x86_64_linux => "x86_64-linux-musl",
            .aarch64_windows => "aarch64-windows-gnu",
            .x86_64_windows => "x86_64-windows-gnu",
            .wasm32_wasi => "wasm32-wasi",
        };
    }

    pub fn exeSuffix(target: Target) []const u8 {
        return switch (target.os()) {
            .windows => ".exe",
            .wasi => ".wasm",
            .linux, .macos => "",
        };
    }

    /// `<arch>-<os>`, as the command line spells one.
    pub fn parse(text: []const u8) ?Target {
        return by_triple.get(text);
    }

    /// For the message when `parse` takes none of them.
    pub const spellings = blk: {
        var text: []const u8 = "";
        for (by_triple.keys()) |key| {
            if (text.len > 0) text = text ++ ", ";
            text = text ++ key;
        }
        break :blk text;
    };

    pub const host: Target = blk: {
        for (std.enums.values(Target)) |target| {
            if (std.mem.eql(u8, @tagName(target.os()), @tagName(builtin.target.os.tag)) and
                std.mem.eql(u8, @tagName(target.arch()), @tagName(builtin.target.cpu.arch)))
            {
                break :blk target;
            }
        }
        @compileError("phi has no name for this host yet: " ++
            @tagName(builtin.target.cpu.arch) ++ "-" ++ @tagName(builtin.target.os.tag));
    };
};

const by_triple = blk: {
    const targets = std.enums.values(Target);
    var entries: [targets.len]struct { []const u8, Target } = undefined;
    for (targets, &entries) |target, *entry| {
        entry.* = .{ @tagName(target.arch()) ++ "-" ++ @tagName(target.os()), target };
    }
    break :blk std.StaticStringMap(Target).initComptime(entries);
};

comptime {
    // a tag says its own arch and os, so the three cannot drift apart
    for (std.enums.values(Target)) |target| {
        const spelled = @tagName(target.arch()) ++ "_" ++ @tagName(target.os());
        assert(std.mem.eql(u8, @tagName(target), spelled));
    }
}

const testing = std.testing;

test "a triple reads back as the target it spells" {
    for (std.enums.values(Target)) |target| {
        var buffer: [64]u8 = undefined;
        const text = try std.fmt.bufPrint(&buffer, "{t}-{t}", .{ target.arch(), target.os() });
        try testing.expectEqual(target, Target.parse(text).?);
        try testing.expect(std.mem.indexOf(u8, Target.spellings, text) != null);
    }
}

test "a pairing that names no machine is refused, along with anything malformed" {
    for ([_][]const u8{
        "",             "-",            "x86_64",       "x86_64-",
        "-macos",       "sparc-macos",  "x86_64-plan9", "x86_64-wasi",
        "wasm32-linux", "x86_64_macos",
    }) |text| {
        try testing.expectEqual(null, Target.parse(text));
    }
}

test "wasm32 is the one target that is not 64-bit, which is why it is here" {
    for (std.enums.values(Target)) |target| {
        const wide: u32 = if (target.arch() == .wasm32) 4 else 8;
        try testing.expectEqual(wide, target.pointerSize());
    }
}

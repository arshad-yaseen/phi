const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const compiler = @import("compiler");
const C = compiler.codegen.C;
const Compilation = compiler.Compilation;
const Target = compiler.Target;

pub const Optimize = enum { fast, small };

pub const Options = struct {
    target: Target = .host,
    optimize: Optimize = .fast,
    /// Where the binary goes, or the entry's stem under the target's suffix.
    out: ?[]const u8 = null,
    /// The one C compiler to run, or the ones tried in turn.
    cc: ?[]const u8 = null,
    keep_c: bool = false,
};

/// What happened, for a caller to say in its own words.
pub const Result = union(enum) {
    built: Built,
    no_entry,
    /// Reported already, so the caller renders what the compilation holds.
    refused,
    overwrites: []const u8,
    no_c_compiler,
    /// The C is kept at this path, for whoever wants to see what was refused.
    c_refused: []const u8,

    pub const Built = struct { path: []const u8, size: ?u64 };
};

pub fn run(
    comp: *Compilation,
    arena: Allocator,
    entry: []const u8,
    options: Options,
) !Result {
    assert(comp.hasErrors() == false);
    assert(entry.len > 0);

    const instance = switch (try C.entryOf(comp)) {
        .instance => |found| found,
        .missing => return .no_entry,
        .refused => return .refused,
    };

    var text: Writer.Allocating = .init(comp.gpa);
    defer text.deinit();
    C.emit(comp, instance, &text.writer) catch |err| switch (err) {
        error.Refused => return .refused,
        error.WriteFailed, error.OutOfMemory => return error.OutOfMemory,
    };

    const out_path = options.out orelse try std.fmt.allocPrint(arena, "{s}{s}", .{
        std.fs.path.stem(entry),
        options.target.exeSuffix(),
    });
    assert(out_path.len > 0);
    if (std.mem.eql(u8, out_path, entry)) return .{ .overwrites = out_path };

    const c_path = try std.fmt.allocPrint(arena, "{s}.c", .{out_path});
    try std.Io.Dir.cwd().writeFile(comp.io, .{ .sub_path = c_path, .data = text.written() });

    switch (try compileC(comp.io, arena, options, c_path, out_path)) {
        .missing => return .no_c_compiler,
        .refused => return .{ .c_refused = c_path },
        .built => {},
    }
    if (options.keep_c == false) std.Io.Dir.cwd().deleteFile(comp.io, c_path) catch {};

    return .{ .built = .{ .path = out_path, .size = sizeOf(comp.io, out_path) } };
}

/// Beside the binary, or in the tree it was built from.
pub fn stdDir(io: std.Io, arena: Allocator) !?[]const u8 {
    if (std.process.executablePathAlloc(io, arena)) |exe_path| {
        if (std.fs.path.dirname(exe_path)) |exe_dir| {
            const beside = try std.fs.path.join(arena, &.{ exe_dir, "..", "lib", "std" });
            if (dirExists(io, beside)) return beside;
        }
    } else |_| {}

    if (dirExists(io, "lib/std")) return "lib/std";
    return null;
}

const Ran = enum { built, refused, missing };

fn compileC(
    io: std.Io,
    arena: Allocator,
    options: Options,
    c_path: []const u8,
    out_path: []const u8,
) !Ran {
    // only `zig cc` builds for a machine it is not running on
    const cross = options.target != Target.host;
    const candidates: []const []const []const u8 = if (options.cc) |chosen|
        &.{&.{chosen}}
    else if (cross)
        &.{&.{ "zig", "cc" }}
    else
        &.{ &.{"cc"}, &.{"clang"}, &.{"gcc"} };

    const optimize: []const u8 = switch (options.optimize) {
        .fast => "-O2",
        .small => "-Os",
    };

    for (candidates) |program| {
        var argv: std.ArrayList([]const u8) = .empty;
        try argv.appendSlice(arena, program);
        try argv.appendSlice(arena, &.{ optimize, "-g", "-w", "-fno-strict-aliasing" });
        if (cross) try argv.appendSlice(arena, &.{ "-target", options.target.cTriple() });
        try argv.appendSlice(arena, &.{ c_path, "-o", out_path });

        var child = std.process.spawn(io, .{ .argv = argv.items }) catch |err| switch (err) {
            error.FileNotFound => continue,
            else => return err,
        };
        return switch (try child.wait(io)) {
            .exited => |code| if (code == 0) .built else .refused,
            else => .refused,
        };
    }
    return .missing;
}

fn sizeOf(io: std.Io, path: []const u8) ?u64 {
    assert(path.len > 0);
    var file = std.Io.Dir.cwd().openFile(io, path, .{ .mode = .read_only }) catch return null;
    defer file.close(io);
    const stat = file.stat(io) catch return null;
    return stat.size;
}

fn dirExists(io: std.Io, path: []const u8) bool {
    assert(path.len > 0);
    var dir = std.Io.Dir.cwd().openDir(io, path, .{}) catch return false;
    dir.close(io);
    return true;
}

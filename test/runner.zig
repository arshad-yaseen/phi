const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const compiler = @import("compiler");

/// The path component after `test/`.
const Kind = enum {
    @"parse-pass",
    @"parse-error",
    ir,
    fail,
    /// A directory of modules entered at `main.phi`.
    multi,
    /// Compiled as though it were the standard library, so a std-only builtin resolves.
    std,

    fn extension(kind: Kind) []const u8 {
        return switch (kind) {
            .@"parse-pass" => ".tree",
            .@"parse-error", .fail, .multi, .std => ".expected",
            .ir => ".ir",
        };
    }

    fn analyzes(kind: Kind) bool {
        return switch (kind) {
            .@"parse-pass", .@"parse-error" => false,
            .ir, .fail, .multi, .std => true,
        };
    }

    /// Where `std.` resolves. A std case is its own standard library.
    fn stdDir(kind: Kind) []const u8 {
        return switch (kind) {
            .std => "test/std",
            else => "lib/std",
        };
    }
};

pub fn main(init: std.process.Init) !u8 {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    assert(args.len > 0);

    var log_buffer: [4096]u8 = undefined;
    var log = std.Io.File.stderr().writer(init.io, &log_buffer);
    defer log.interface.flush() catch {};

    var update = false;
    var failures: u32 = 0;
    var ran: u32 = 0;

    for (args[1..]) |argument| {
        if (std.mem.eql(u8, argument, "--update")) {
            update = true;
            continue;
        }

        ran += 1;
        const passed = try runOne(init.gpa, init.io, argument, update, &log.interface);
        if (passed == false) failures += 1;
    }

    assert(ran >= failures);
    if (failures > 0) {
        try log.interface.print("{d} of {d} file tests failed\n", .{ failures, ran });
        return 1;
    }
    return 0;
}

fn runOne(
    gpa: Allocator,
    io: std.Io,
    path: []const u8,
    update: bool,
    log: *Writer,
) !bool {
    assert(path.len > ".phi".len);
    assert(std.mem.endsWith(u8, path, ".phi"));
    const kind = kindOf(path) orelse {
        try log.print("{s}: not under a directory the runner knows\n", .{path});
        return false;
    };

    var actual: Writer.Allocating = .init(gpa);
    defer actual.deinit();

    const produced = if (kind.analyzes())
        try runCompile(gpa, io, path, kind, &actual.writer, log)
    else
        try runParse(gpa, io, path, kind, &actual.writer, log);
    if (produced == false) return false;

    const golden_path = try std.fmt.allocPrint(gpa, "{s}{s}", .{
        path[0 .. path.len - ".phi".len],
        kind.extension(),
    });
    defer gpa.free(golden_path);

    if (update) {
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = golden_path, .data = actual.written() });
        return true;
    }

    const golden = std.Io.Dir.cwd().readFileAlloc(io, golden_path, gpa, .limited(1 << 22)) catch {
        try log.print("{s}: no golden yet, run 'zig build test-update'\n", .{golden_path});
        return false;
    };
    defer gpa.free(golden);

    if (std.mem.eql(u8, golden, actual.written())) return true;

    try log.print("{s}: does not match\n--- expected ---\n{s}--- actual ---\n{s}---\n", .{
        golden_path, golden, actual.written(),
    });
    return false;
}

fn runParse(
    gpa: Allocator,
    io: std.Io,
    path: []const u8,
    kind: Kind,
    actual: *Writer,
    log: *Writer,
) !bool {
    var source: compiler.Source = try .load(gpa, io, .cwd(), path);
    defer source.deinit(gpa);

    var tree = try compiler.AST.parse(gpa, source.bytes);
    defer tree.deinit(gpa);

    // the dump has to survive a tree made mostly of holes
    var sink: Writer.Discarding = .init(&.{});
    try compiler.spell.writeTree(tree, &sink.writer);

    switch (kind) {
        .@"parse-pass" => {
            if (tree.errors.len > 0) {
                try log.print("{s}: expected to parse, but\n", .{path});
                for (tree.errors) |diagnostic| {
                    try diagnostic.render(gpa, &source, log, .off);
                }
                return false;
            }
            try compiler.spell.writeTree(tree, actual);
        },
        .@"parse-error" => {
            if (tree.errors.len == 0) {
                try log.print("{s}: expected a diagnostic, got none\n", .{path});
                return false;
            }
            for (tree.errors) |diagnostic| try diagnostic.render(gpa, &source, actual, .off);
        },
        else => unreachable,
    }
    return true;
}

/// The whole pipeline, against the repository's own `lib/std`.
fn runCompile(
    gpa: Allocator,
    io: std.Io,
    path: []const u8,
    kind: Kind,
    actual: *Writer,
    log: *Writer,
) !bool {
    const source: compiler.Source = try .load(gpa, io, .cwd(), path);

    var comp: compiler.Compilation = undefined;
    try comp.init(gpa, io, .{ .root_path = path, .std_dir = kind.stdDir() });
    defer comp.deinit();
    try comp.compile(source);

    const failed = comp.hasErrors();
    switch (kind) {
        .ir => {
            if (failed) {
                try log.print("{s}: expected to compile, but\n", .{path});
                try comp.renderAll(log, .off);
                return false;
            }
            try comp.dumpIR(actual);
        },
        .fail => {
            if (failed == false) {
                try log.print("{s}: expected a diagnostic, got none\n", .{path});
                return false;
            }
            try comp.renderAll(actual, .off);
        },
        .multi, .std => if (failed) {
            try comp.renderAll(actual, .off);
        } else {
            try comp.dumpIR(actual);
        },
        else => unreachable,
    }
    return true;
}

fn kindOf(path: []const u8) ?Kind {
    assert(path.len > 0);
    if (std.mem.endsWith(u8, path, ".phi") == false) return null;

    var components = std.mem.splitScalar(u8, path, '/');
    const first = components.next() orelse return null;
    if (std.mem.eql(u8, first, "test") == false) return null;
    const second = components.next() orelse return null;
    return std.meta.stringToEnum(Kind, second);
}

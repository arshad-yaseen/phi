//! Runs the file tests. A case is a `.phi` file, or a directory holding a
//! `main.phi`, and the goldens beside it say everything, each golden's
//! extension names one assertion, so directories are free grouping and the
//! runner never reads their names. A new case opts in by touching the golden
//! it expects, then `zig build test-update` fills it.

const std = @import("std");
const assert = std.debug.assert;
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const compiler = @import("compiler");

/// Cases under here compile as the standard library, and are their own std.
const std_root = "test/std";

/// What one golden asserts of its case.
const Golden = enum {
    /// The parse tree. The case must parse clean. Nothing is compiled
    /// unless another golden asks.
    tree,
    /// Rendered diagnostics. The case must fail to compile.
    expected,
    /// The typed IR. The case must compile.
    ir,
    /// The C the backend emits. The case must compile, and have a `main`.
    c,
    /// What the program prints. Compiled with `zig cc`, run, must exit clean.
    out,
    /// What the program prints before it stops. The run must end at a trap.
    trap,

    fn extension(golden: Golden) []const u8 {
        return switch (golden) {
            .tree => ".tree",
            .expected => ".expected",
            .ir => ".ir",
            .c => ".c",
            .out => ".out",
            .trap => ".trap",
        };
    }
};

const GoldenSet = std.EnumSet(Golden);

/// Directories nest cases a few levels at most, far under this.
const walk_depth_max = 8;

pub fn main(init: std.process.Init) !u8 {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    assert(args.len > 0);

    var log_buffer: [4096]u8 = undefined;
    var log = std.Io.File.stderr().writer(init.io, &log_buffer);
    defer log.interface.flush() catch {};

    const arena = init.arena.allocator();
    var cases: std.ArrayList([]const u8) = .empty;

    var update = false;
    for (args[1..]) |argument| {
        if (std.mem.eql(u8, argument, "--update")) {
            update = true;
            continue;
        }
        if (std.mem.endsWith(u8, argument, ".phi")) {
            try cases.append(arena, argument);
            continue;
        }
        try collectCases(arena, init.io, &cases, argument, 0);
    }
    std.mem.sort([]const u8, cases.items, {}, stringLessThan);

    var failures: u32 = 0;
    for (cases.items) |path| {
        const passed = try runOne(init.gpa, init.io, path, update, &log.interface);
        if (passed == false) failures += 1;
    }

    assert(cases.items.len >= failures);
    if (failures > 0) {
        try log.interface.print("{d} of {d} file tests failed\n", .{
            failures,
            cases.items.len,
        });
        return 1;
    }
    return 0;
}

/// Every case under `path`. A directory holding `main.phi` is one case,
/// entered there, and its other files are the modules it imports.
fn collectCases(
    arena: Allocator,
    io: std.Io,
    cases: *std.ArrayList([]const u8),
    path: []const u8,
    depth: u32,
) !void {
    assert(path.len > 0);
    assert(depth < walk_depth_max);

    var dir = try std.Io.Dir.cwd().openDir(io, path, .{ .iterate = true });
    defer dir.close(io);

    if (dir.access(io, "main.phi", .{})) |_| {
        try cases.append(arena, try std.fmt.allocPrint(arena, "{s}/main.phi", .{path}));
        return;
    } else |_| {}

    var walk = dir.iterate();
    while (walk.next(io) catch null) |entry| {
        const sub = try std.fmt.allocPrint(arena, "{s}/{s}", .{ path, entry.name });
        if (entry.kind == .directory) {
            try collectCases(arena, io, cases, sub, depth + 1);
            continue;
        }
        if (entry.kind != .file) continue;
        if (std.mem.endsWith(u8, entry.name, ".phi") == false) continue;
        try cases.append(arena, sub);
    }
}

fn stringLessThan(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.lessThan(u8, a, b);
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
    const stem = path[0 .. path.len - ".phi".len];

    var goldens: GoldenSet = .initEmpty();
    for (std.enums.values(Golden)) |golden| {
        const golden_path = try std.fmt.allocPrint(gpa, "{s}{s}", .{
            stem,
            golden.extension(),
        });
        defer gpa.free(golden_path);
        if (std.Io.Dir.cwd().access(io, golden_path, .{})) |_| {
            goldens.insert(golden);
        } else |_| {}
    }

    if (goldens.count() == 0) {
        try log.print("{s}: no golden says what this case expects, touch one of " ++
            ".tree .expected .ir .c .out .trap beside it\n", .{path});
        return false;
    }
    // a case fails or it does not, so diagnostics exclude every other product
    const products = GoldenSet.initMany(&.{ .ir, .c, .out, .trap });
    if (goldens.contains(.expected) and goldens.intersectWith(products).count() > 0) {
        try log.print("{s}: '.expected' asserts failure, which no other golden survives\n", .{
            path,
        });
        return false;
    }
    if (goldens.contains(.out) and goldens.contains(.trap)) {
        try log.print("{s}: one run exits clean or traps, never both\n", .{path});
        return false;
    }

    if (goldens.count() == 1 and goldens.contains(.tree)) {
        return runParse(gpa, io, path, stem, update, log);
    }
    return runCompile(gpa, io, path, stem, goldens, update, log);
}

/// A grammar case. Parsed, never compiled, so its names need not resolve.
fn runParse(
    gpa: Allocator,
    io: std.Io,
    path: []const u8,
    stem: []const u8,
    update: bool,
    log: *Writer,
) !bool {
    var source: compiler.Source = try .load(gpa, io, .cwd(), path);
    defer source.deinit(gpa);

    var ast = try compiler.AST.parse(gpa, source.bytes);
    defer ast.deinit(gpa);

    if (ast.errors.len > 0) {
        try log.print("{s}: expected to parse, but\n", .{path});
        for (ast.errors) |diagnostic| try diagnostic.render(gpa, &source, log, .off);
        return false;
    }

    var actual: Writer.Allocating = .init(gpa);
    defer actual.deinit();
    try compiler.Spell.writeTree(ast, &actual.writer);
    return settle(gpa, io, stem, .tree, actual.written(), update, log);
}

/// The whole pipeline, each present golden checked against one compilation.
fn runCompile(
    gpa: Allocator,
    io: std.Io,
    path: []const u8,
    stem: []const u8,
    goldens: GoldenSet,
    update: bool,
    log: *Writer,
) !bool {
    const source: compiler.Source = try .load(gpa, io, .cwd(), path);

    const in_std = std.mem.startsWith(u8, path, std_root ++ "/");
    var comp: compiler.Compilation = undefined;
    try comp.init(gpa, io, .{
        .root_path = path,
        .std_dir = if (in_std) std_root else "lib/std",
    });
    defer comp.deinit();
    try comp.compile(source);

    // the dump has to survive whatever tree recovery left behind
    var sink: Writer.Discarding = .init(&.{});
    try compiler.Spell.writeTree(comp.moduleAt(.root).tree, &sink.writer);

    var ok = true;
    if (goldens.contains(.tree)) {
        const tree = comp.moduleAt(.root).tree;
        if (tree.errors.len > 0) {
            try log.print("{s}: expected to parse, but\n", .{path});
            try comp.renderAll(log, .off);
            return false;
        }
        var actual: Writer.Allocating = .init(gpa);
        defer actual.deinit();
        try compiler.Spell.writeTree(tree, &actual.writer);
        if (try settle(gpa, io, stem, .tree, actual.written(), update, log) == false) {
            ok = false;
        }
    }

    if (goldens.contains(.expected)) {
        if (comp.hasErrors() == false) {
            try log.print("{s}: expected a diagnostic, got none\n", .{path});
            return false;
        }
        var actual: Writer.Allocating = .init(gpa);
        defer actual.deinit();
        try comp.renderAll(&actual.writer, .off);
        if (try settle(gpa, io, stem, .expected, actual.written(), update, log) == false) {
            ok = false;
        }
        return ok;
    }

    if (comp.hasErrors()) {
        try log.print("{s}: expected to compile, but\n", .{path});
        try comp.renderAll(log, .off);
        return false;
    }

    if (goldens.contains(.ir)) {
        var actual: Writer.Allocating = .init(gpa);
        defer actual.deinit();
        try comp.dumpIR(&actual.writer);
        if (try settle(gpa, io, stem, .ir, actual.written(), update, log) == false) {
            ok = false;
        }
    }

    const wants_backend = goldens.intersectWith(GoldenSet.initMany(&.{
        .c, .out, .trap,
    })).count() > 0;
    if (wants_backend) {
        if (try runBackend(gpa, io, &comp, path, stem, goldens, update, log) == false) {
            ok = false;
        }
    }
    return ok;
}

fn runBackend(
    gpa: Allocator,
    io: std.Io,
    comp: *compiler.Compilation,
    path: []const u8,
    stem: []const u8,
    goldens: GoldenSet,
    update: bool,
    log: *Writer,
) !bool {
    const entry = switch (try compiler.backend.C.entryOf(comp)) {
        .instance => |instance| instance,
        .missing => {
            try log.print("{s}: a backend case needs a 'fn main'\n", .{path});
            return false;
        },
        .refused => {
            try comp.renderAll(log, .off);
            return false;
        },
    };

    var c_text: Writer.Allocating = .init(gpa);
    defer c_text.deinit();
    compiler.backend.C.emit(comp, entry, &c_text.writer) catch |err| switch (err) {
        error.Refused => {
            try comp.renderAll(log, .off);
            return false;
        },
        error.WriteFailed, error.OutOfMemory => return error.OutOfMemory,
    };

    var ok = true;
    if (goldens.contains(.c)) {
        if (try settle(gpa, io, stem, .c, c_text.written(), update, log) == false) {
            ok = false;
        }
    }

    const runs = goldens.contains(.out) or goldens.contains(.trap);
    if (runs == false) return ok;

    const work_dir = ".zig-cache/phi-exec";
    try std.Io.Dir.cwd().createDirPath(io, work_dir);

    // the whole path, so cases in different directories never share a binary
    const flat = try gpa.dupe(u8, stem);
    defer gpa.free(flat);
    std.mem.replaceScalar(u8, flat, '/', '_');
    std.mem.replaceScalar(u8, flat, '.', '_');

    const c_path = try std.fmt.allocPrint(gpa, "{s}/{s}.c", .{ work_dir, flat });
    defer gpa.free(c_path);
    const binary_suffix = if (builtin.os.tag == .windows) ".exe" else "";
    const binary_path = try std.fmt.allocPrint(gpa, "{s}/{s}{s}", .{
        work_dir, flat, binary_suffix,
    });
    defer gpa.free(binary_path);

    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = c_path, .data = c_text.written() });

    const compiled = (try runChecked(gpa, io, &.{
        "zig", "cc", "-w", c_path, "-o", binary_path,
    }, path, "zig cc refused the generated C", log)) orelse return false;
    gpa.free(compiled);

    if (goldens.contains(.trap)) {
        const result = try std.process.run(gpa, io, .{ .argv = &.{binary_path} });
        defer gpa.free(result.stdout);
        defer gpa.free(result.stderr);
        if (result.term == .exited and result.term.exited == 0) {
            try log.print("{s}: expected the program to stop at a trap\n", .{path});
            return false;
        }
        const shown = try programOutput(gpa, result.stdout);
        defer gpa.free(shown);
        if (try settle(gpa, io, stem, .trap, shown, update, log) == false) ok = false;
        return ok;
    }

    const output = (try runChecked(gpa, io, &.{binary_path}, path, "the program did not " ++
        "exit cleanly", log)) orelse return false;
    defer gpa.free(output);

    const shown = try programOutput(gpa, output);
    defer gpa.free(shown);
    if (try settle(gpa, io, stem, .out, shown, update, log) == false) ok = false;
    return ok;
}

/// Windows text mode writes \r\n, so the goldens read platform newlines alike.
fn programOutput(gpa: Allocator, output: []const u8) ![]u8 {
    if (builtin.os.tag == .windows) {
        return std.mem.replaceOwned(u8, gpa, output, "\r\n", "\n");
    }
    return gpa.dupe(u8, output);
}

/// One golden compared, or rewritten under `--update`.
fn settle(
    gpa: Allocator,
    io: std.Io,
    stem: []const u8,
    golden: Golden,
    actual: []const u8,
    update: bool,
    log: *Writer,
) !bool {
    const golden_path = try std.fmt.allocPrint(gpa, "{s}{s}", .{ stem, golden.extension() });
    defer gpa.free(golden_path);

    if (update) {
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = golden_path, .data = actual });
        return true;
    }

    const golden_text = std.Io.Dir.cwd().readFileAlloc(io, golden_path, gpa, .limited(1 << 22)) catch {
        try log.print("{s}: no golden yet, run 'zig build test-update'\n", .{golden_path});
        return false;
    };
    defer gpa.free(golden_text);

    if (std.mem.eql(u8, golden_text, actual)) return true;

    try log.print("{s}: does not match\n--- expected ---\n{s}--- actual ---\n{s}---\n", .{
        golden_path, golden_text, actual,
    });
    return false;
}

/// Runs the argv and hands back its stdout, or logs what refused and why.
fn runChecked(
    gpa: Allocator,
    io: std.Io,
    argv: []const []const u8,
    path: []const u8,
    complaint: []const u8,
    log: *Writer,
) !?[]u8 {
    const result = try std.process.run(gpa, io, .{ .argv = argv });
    defer gpa.free(result.stderr);
    if (result.term == .exited and result.term.exited == 0) return result.stdout;

    gpa.free(result.stdout);
    try log.print("{s}: {s}\n{s}", .{ path, complaint, result.stderr });
    return null;
}

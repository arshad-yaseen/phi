const std = @import("std");
const assert = std.debug.assert;
const Writer = std.Io.Writer;

const build_options = @import("build_options");
const compiler = @import("compiler");

pub fn main(init: std.process.Init) !u8 {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    assert(args.len > 0);

    var out_buffer: [4096]u8 = undefined;
    var out = std.Io.File.stdout().writer(init.io, &out_buffer);

    var log_buffer: [4096]u8 = undefined;
    var log = std.Io.File.stderr().writer(init.io, &log_buffer);

    const status = run(init, args, &out.interface, &log.interface) catch |err| status: {
        try log.interface.print("phi: {t}\n", .{err});
        break :status 2;
    };

    try out.interface.flush();
    try log.interface.flush();
    return status;
}

const usage =
    \\usage: phi <command> <entry>
    \\
    \\An entry is one file. Everything it imports is part of the program.
    \\
    \\commands:
    \\  check <entry>   check the program and report what is wrong
    \\  ir    <entry>   print the typed IR
    \\  build <entry>   compile the program to a native binary
    \\  run   <entry>   build the program, then run it
    \\
    \\options:
    \\  --std <dir>           where the standard library lives
    \\  --color auto|on|off   colour the output (default: auto)
    \\  --opt fast|small      what the C compiler optimizes for (default: fast)
    \\  --out <path>          where the binary goes (default: the entry's stem)
    \\  --cc <path>           the C compiler to use (default: cc, clang, or gcc)
    \\  --emit-c              keep the generated C beside the binary
    \\  --version             print the version
    \\
;

const Command = enum { check, ir, build, run };

const ColorChoice = enum { auto, on, off };

/// What the C compiler is asked to favour.
const Optimize = enum { fast, small };

const Request = struct {
    command: Command,
    path: []const u8,
    color: ColorChoice,
    optimize: Optimize,
    std_dir: ?[]const u8,
    out: ?[]const u8,
    cc: ?[]const u8,
    emit_c: bool,
};

const clock: std.Io.Clock = .awake;

fn run(init: std.process.Init, args: []const [:0]const u8, out: *Writer, log: *Writer) !u8 {
    const request = switch (try readArgs(args, out, log)) {
        .ready => |request| request,
        .done => |status| return status,
    };

    const start = clock.now(init.io);

    const source: compiler.Source = compiler.Source.load(
        init.gpa,
        init.io,
        .cwd(),
        request.path,
    ) catch |err| switch (err) {
        error.ReadFailed => {
            try log.print("phi: cannot read '{s}'\n", .{request.path});
            return 2;
        },
        error.SourceTooLarge => {
            try log.print("phi: '{s}' is larger than the compiler can index\n", .{request.path});
            return 2;
        },
        error.OutOfMemory => return err,
    };

    var comp: compiler.Compilation = undefined;
    try comp.init(init.gpa, init.io, .{
        .root_path = request.path,
        .std_dir = request.std_dir orelse try findStd(init),
    });
    defer comp.deinit();

    // the compilation owns the root source from here
    try comp.compile(source);

    const color: compiler.Diagnostic.Color = switch (request.color) {
        .on => .on,
        .off => .off,
        .auto => if (try std.Io.File.stderr().isTty(init.io)) .on else .off,
    };
    if (comp.hasErrors()) {
        try comp.renderAll(log, color);
        return 1;
    }

    switch (request.command) {
        .check, .ir => {
            if (request.command == .ir) try comp.dumpIR(out);
            const elapsed = start.untilNow(init.io, clock);
            assert(elapsed.nanoseconds >= 0);
            try log.print("checked in {f}\n", .{elapsed});
            return 0;
        },
        .build, .run => return runBuild(init, &comp, request, log, color, start),
    }
}

/// emit C, hand it to a C compiler, maybe run it.
fn runBuild(
    init: std.process.Init,
    comp: *compiler.Compilation,
    request: Request,
    log: *Writer,
    color: compiler.Diagnostic.Color,
    start: std.Io.Timestamp,
) !u8 {
    const arena = init.arena.allocator();
    assert(comp.hasErrors() == false);

    const entry = switch (try compiler.backend.C.entryOf(comp)) {
        .instance => |instance| instance,
        .missing => {
            try log.print("phi: '{s}' has no 'fn main' to start from\n", .{request.path});
            return 1;
        },
        .refused => {
            try comp.renderAll(log, color);
            return 1;
        },
    };

    var c_text: Writer.Allocating = .init(init.gpa);
    defer c_text.deinit();
    compiler.backend.C.emit(comp, entry, &c_text.writer) catch |err| switch (err) {
        error.Refused => {
            try comp.renderAll(log, color);
            return 1;
        },
        // the buffer's writes fail only when its allocation does
        error.WriteFailed, error.OutOfMemory => return error.OutOfMemory,
    };

    const out_path = request.out orelse std.fs.path.stem(request.path);
    assert(out_path.len > 0);
    if (std.mem.eql(u8, out_path, request.path)) {
        try log.print("phi: building '{s}' would overwrite the entry\n", .{out_path});
        return 2;
    }

    const c_path = try std.fmt.allocPrint(arena, "{s}.c", .{out_path});
    try std.Io.Dir.cwd().writeFile(init.io, .{ .sub_path = c_path, .data = c_text.written() });

    const status = compileC(init, request, c_path, out_path, log) catch |err| {
        try log.print("phi: cannot run a C compiler: {t}\n", .{err});
        return 2;
    };
    if (status != 0) {
        try log.print("phi: the C compiler refused '{s}', which is kept to inspect\n", .{c_path});
        return 2;
    }
    if (request.emit_c == false) {
        std.Io.Dir.cwd().deleteFile(init.io, c_path) catch {};
    }

    if (request.command == .build) {
        const elapsed = start.untilNow(init.io, clock);
        assert(elapsed.nanoseconds >= 0);
        try log.print("built '{s}' in {f}\n", .{ out_path, elapsed });
        return 0;
    }

    // a separator makes argv[0] a path, so the binary just built is the one run
    const program = if (std.fs.path.dirname(out_path) == null)
        try std.fmt.allocPrint(arena, "./{s}", .{out_path})
    else
        out_path;

    // the program owns the terminal from here, so nothing is printed around it
    var child = try std.process.spawn(init.io, .{ .argv = &.{program} });
    switch (try child.wait(init.io)) {
        .exited => |code| return code,
        .signal => |signal| {
            try log.print("phi: the program stopped at a trap\n", .{});
            // the shell convention, 128 plus the signal
            return @intCast(128 + (@intFromEnum(signal) & 0x3f));
        },
        else => {
            try log.print("phi: the program did not exit\n", .{});
            return 2;
        },
    }
}

fn compileC(
    init: std.process.Init,
    request: Request,
    c_path: []const u8,
    out_path: []const u8,
    log: *Writer,
) !u8 {
    const candidates: []const []const u8 = if (request.cc) |chosen|
        &.{chosen}
    else
        &.{ "cc", "clang", "gcc" };

    const optimize: []const u8 = switch (request.optimize) {
        .fast => "-O2",
        .small => "-Os",
    };

    for (candidates) |candidate| {
        const argv = [_][]const u8{ candidate, optimize, "-w", c_path, "-o", out_path };
        var child = std.process.spawn(init.io, .{ .argv = &argv }) catch |err| switch (err) {
            error.FileNotFound => continue,
            else => return err,
        };
        return switch (try child.wait(init.io)) {
            .exited => |code| code,
            else => 1,
        };
    }

    try log.print("phi: no C compiler found, so pass one with --cc <path>\n", .{});
    return 2;
}

/// Beside the binary as `../lib/std`, or `lib/std` under the working directory.
fn findStd(init: std.process.Init) !?[]const u8 {
    const arena = init.arena.allocator();

    if (std.process.executablePathAlloc(init.io, arena)) |exe_path| {
        if (std.fs.path.dirname(exe_path)) |exe_dir| {
            const beside = try std.fs.path.join(arena, &.{ exe_dir, "..", "lib", "std" });
            if (dirExists(init.io, beside)) return beside;
        }
    } else |_| {}

    if (dirExists(init.io, "lib/std")) return "lib/std";
    return null;
}

fn dirExists(io: std.Io, path: []const u8) bool {
    assert(path.len > 0);
    var dir = std.Io.Dir.cwd().openDir(io, path, .{}) catch return false;
    dir.close(io);
    return true;
}

const ArgsResult = union(enum) { ready: Request, done: u8 };

fn readArgs(args: []const [:0]const u8, out: *Writer, log: *Writer) !ArgsResult {
    assert(args.len > 0);
    assert(out != log);

    var command: ?Command = null;
    var path: ?[]const u8 = null;
    var color: ColorChoice = .auto;
    var optimize: Optimize = .fast;
    var std_dir: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var cc: ?[]const u8 = null;
    var emit_c = false;

    var index: u32 = 1;
    arguments: while (index < args.len) : (index += 1) {
        const argument = args[index];

        if (std.mem.eql(u8, argument, "--version")) {
            try out.print("{s}\n", .{build_options.version});
            return .{ .done = 0 };
        }
        if (std.mem.eql(u8, argument, "--emit-c")) {
            emit_c = true;
            continue;
        }

        inline for (.{
            .{ "--color", &color, "a setting", "--color takes auto, on, or off" },
            .{ "--opt", &optimize, "a setting", "--opt takes fast or small" },
            .{ "--std", &std_dir, "a directory", {} },
            .{ "--out", &out_path, "a path", {} },
            .{ "--cc", &cc, "a path", {} },
        }) |option| {
            const name, const target, const wants, const takes = option;
            if (std.mem.eql(u8, argument, name)) {
                index += 1;
                if (index == args.len) {
                    return .{ .done = try misuse(log, name ++ " needs " ++ wants) };
                }
                if (@TypeOf(takes) == void) {
                    target.* = args[index];
                } else {
                    target.* = std.meta.stringToEnum(@TypeOf(target.*), args[index]) orelse {
                        return .{ .done = try misuse(log, takes) };
                    };
                }
                continue :arguments;
            }
        }

        if (command == null) {
            command = std.meta.stringToEnum(Command, argument) orelse {
                return .{ .done = try misuse(log, "no such command") };
            };
            continue;
        }
        if (path != null) return .{ .done = try misuse(log, "one entry at a time") };
        path = argument;
    }

    return .{ .ready = .{
        .command = command orelse return .{ .done = try misuse(log, "no command given") },
        .path = path orelse return .{ .done = try misuse(log, "no entry given") },
        .color = color,
        .optimize = optimize,
        .std_dir = std_dir,
        .out = out_path,
        .cc = cc,
        .emit_c = emit_c,
    } };
}

fn misuse(log: *Writer, problem: []const u8) Writer.Error!u8 {
    assert(problem.len > 0);
    try log.print("phi: {s}\n\n{s}", .{ problem, usage });
    return 2;
}

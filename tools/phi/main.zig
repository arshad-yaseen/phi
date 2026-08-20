const std = @import("std");
const assert = std.debug.assert;
const Writer = std.Io.Writer;

const build_options = @import("build_options");
const compiler = @import("compiler");

const Build = @import("Build.zig");
const Target = compiler.Target;

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
    \\
    \\options:
    \\  --target <arch>-<os>  what to build for (default: this machine)
    \\  --std <dir>           where the standard library lives
    \\  --color auto|on|off   colour the output (default: auto)
    \\  --opt fast|small      what the C compiler optimizes for (default: fast)
    \\  --out <path>          where the binary goes (default: the entry's stem)
    \\  --cc <path>           the C compiler to use (default: cc, clang, or gcc)
    \\  --emit-c              keep the generated C beside the binary
    \\  --version             print the version
    \\
;

const Command = enum { check, ir, build };

const ColorChoice = enum { auto, on, off };

const Request = struct {
    command: Command,
    path: []const u8,
    color: ColorChoice,
    std_dir: ?[]const u8,
    build: Build.Options,
};

const clock: std.Io.Clock = .awake;

fn run(init: std.process.Init, args: []const [:0]const u8, out: *Writer, log: *Writer) !u8 {
    const request = switch (try readArgs(args, out, log)) {
        .ready => |ready| ready,
        .done => |status| return status,
    };

    const start = clock.now(init.io);

    const source: compiler.Source = compiler.Source.load(
        init.gpa,
        init.io,
        .cwd(),
        request.path,
    ) catch |err| switch (err) {
        error.ReadFailed => return say(log, "cannot read '{s}'", .{request.path}),
        error.SourceTooLarge => {
            return say(log, "'{s}' is larger than the compiler can index", .{request.path});
        },
        error.OutOfMemory => return err,
    };

    var comp: compiler.Compilation = undefined;
    try comp.init(init.gpa, init.io, .{
        .root_path = request.path,
        .std_dir = request.std_dir orelse try Build.stdDir(init.io, init.arena.allocator()),
        .target = request.build.target,
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

    if (request.command == .ir) try comp.dumpIR(out);
    if (request.command != .build) {
        try log.print("checked in {f}\n", .{start.untilNow(init.io, clock)});
        return 0;
    }

    const result = try Build.run(&comp, init.arena.allocator(), request.path, request.build);
    return report(&comp, result, log, color, start.untilNow(init.io, clock));
}

fn report(
    comp: *compiler.Compilation,
    result: Build.Result,
    log: *Writer,
    color: compiler.Diagnostic.Color,
    elapsed: std.Io.Duration,
) !u8 {
    switch (result) {
        .built => |binary| {
            const bytes = binary.size orelse {
                try log.print("built '{s}' in {f}\n", .{ binary.path, elapsed });
                return 0;
            };
            var buffer: [32]u8 = undefined;
            try log.print("built '{s}' ({s}) in {f}\n", .{
                binary.path,
                sizeText(&buffer, bytes),
                elapsed,
            });
            return 0;
        },
        .no_entry => return say(log, "nothing to start from, so write 'fn main()'", .{}),
        .refused => {
            try comp.renderAll(log, color);
            return 1;
        },
        .overwrites => |path| return say(log, "building '{s}' would overwrite the entry", .{path}),
        .no_c_compiler => return say(log, "no C compiler found, so pass one with --cc <path>", .{}),
        .c_refused => |path| {
            return say(log, "the C compiler refused '{s}', which is kept to inspect", .{path});
        },
    }
}

fn say(log: *Writer, comptime template: []const u8, args: anytype) !u8 {
    try log.print("phi: " ++ template ++ "\n", args);
    return 2;
}

fn sizeText(buffer: []u8, bytes: u64) []const u8 {
    assert(buffer.len >= 32);
    if (bytes < 1024) {
        return std.fmt.bufPrint(buffer, "{d} B", .{bytes}) catch unreachable;
    }
    const kib = @as(f64, @floatFromInt(bytes)) / 1024.0;
    if (kib < 1024.0) {
        return std.fmt.bufPrint(buffer, "{d:.1} KiB", .{kib}) catch unreachable;
    }
    return std.fmt.bufPrint(buffer, "{d:.1} MiB", .{kib / 1024.0}) catch unreachable;
}

const ArgsResult = union(enum) { ready: Request, done: u8 };

fn readArgs(args: []const [:0]const u8, out: *Writer, log: *Writer) !ArgsResult {
    assert(args.len > 0);
    assert(out != log);

    var command: ?Command = null;
    var path: ?[]const u8 = null;
    var color: ColorChoice = .auto;
    var std_dir: ?[]const u8 = null;
    var options: Build.Options = .{};

    var index: u32 = 1;
    arguments: while (index < args.len) : (index += 1) {
        const argument = args[index];

        if (std.mem.eql(u8, argument, "--version")) {
            try out.print("{s}\n", .{build_options.version});
            return .{ .done = 0 };
        }
        if (std.mem.eql(u8, argument, "--emit-c")) {
            options.keep_c = true;
            continue;
        }
        if (std.mem.eql(u8, argument, "--target")) {
            index += 1;
            if (index == args.len) return .{ .done = try misuse(log, "--target needs a triple") };
            options.target = Target.parse(args[index]) orelse {
                return .{ .done = try misuse(log, target_help) };
            };
            continue;
        }

        inline for (.{
            .{ "--color", &color, "a setting", "--color takes auto, on, or off" },
            .{ "--opt", &options.optimize, "a setting", "--opt takes fast or small" },
            .{ "--std", &std_dir, "a directory", {} },
            .{ "--out", &options.out, "a path", {} },
            .{ "--cc", &options.cc, "a path", {} },
        }) |option| {
            const name, const slot, const wants, const takes = option;
            if (std.mem.eql(u8, argument, name)) {
                index += 1;
                if (index == args.len) {
                    return .{ .done = try misuse(log, name ++ " needs " ++ wants) };
                }
                if (@TypeOf(takes) == void) {
                    slot.* = args[index];
                } else {
                    slot.* = std.meta.stringToEnum(@TypeOf(slot.*), args[index]) orelse {
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
        .std_dir = std_dir,
        .build = options,
    } };
}

const target_help = "--target takes <arch>-<os>, one of " ++ Target.spellings;

fn misuse(log: *Writer, problem: []const u8) Writer.Error!u8 {
    assert(problem.len > 0);
    try log.print("phi: {s}\n\n{s}", .{ problem, usage });
    return 2;
}

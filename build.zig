const std = @import("std");

const zon = @import("build.zig.zon");

/// Room for the deepest analysis recursion the parser allows.
const analysis_stack_bytes = 128 << 20;

const release_targets = [_][]const u8{
    "aarch64-macos",
    "x86_64-macos",
    "aarch64-linux-musl",
    "x86_64-linux-musl",
    "x86_64-windows",
};

const release_docs = [_][]const u8{ "README.md", "LICENSE" };

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const version = resolveVersion(b);

    const options = b.addOptions();
    options.addOption([]const u8, "version", version);
    // one module per compile, because two roots over one file are two modules
    const build_options = options.createModule();

    const compiler = b.addModule("compiler", .{
        .root_source_file = b.path("compiler/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe = b.addExecutable(.{
        .name = "phi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("tools/phi/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = compiler },
                .{ .name = "build_options", .module = build_options },
            },
        }),
    });
    exe.stack_size = analysis_stack_bytes;
    b.installArtifact(exe);

    b.installDirectory(.{
        .source_dir = b.path("lib"),
        .install_dir = .prefix,
        .install_subdir = "lib",
    });

    const run = b.addRunArtifact(exe);
    run.step.dependOn(b.getInstallStep());
    if (b.args) |args| run.addArgs(args);
    b.step("run", "Build and run phi").dependOn(&run.step);

    const test_step = b.step("test", "Run unit tests and file tests");

    const unit = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("compiler/root.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    unit.stack_size = analysis_stack_bytes;
    test_step.dependOn(&b.addRunArtifact(unit).step);

    const runner = b.addExecutable(.{
        .name = "filetest",
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/runner.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "compiler", .module = compiler }},
        }),
    });
    runner.stack_size = analysis_stack_bytes;

    const file_tests = b.addRunArtifact(runner);
    addTestFiles(b, file_tests);
    test_step.dependOn(&file_tests.step);

    const update = b.addRunArtifact(runner);
    update.addArg("--update");
    addTestFiles(b, update);
    b.step("test-update", "Rewrite what the file tests expect").dependOn(&update.step);

    addRelease(b, version, options);
}

fn addRelease(b: *std.Build, version: []const u8, options: *std.Build.Step.Options) void {
    const release_step = b.step("release", "Cross-compile a release tree for every target");

    const stamp = b.addWriteFiles().add("version.txt", b.fmt("{s}\n", .{version}));
    release_step.dependOn(&b.addInstallFile(stamp, "release/version.txt").step);

    // GitHub renames a release asset whose name holds a `+`, so paths avoid one
    const in_paths = b.allocator.dupe(u8, version) catch @panic("OOM");
    std.mem.replaceScalar(u8, in_paths, '+', '.');

    for (release_targets) |triple| {
        const query = std.Target.Query.parse(.{ .arch_os_abi = triple }) catch
            std.debug.panic("release target '{s}' is not a target triple", .{triple});
        const exe = addPhi(b, b.resolveTargetQuery(query), .ReleaseFast, options);

        const tree = b.fmt("release/phi-{s}-{s}", .{ in_paths, triple });
        const binary = b.addInstallArtifact(exe, .{
            .dest_dir = .{ .override = .{ .custom = b.fmt("{s}/bin", .{tree}) } },
        });
        release_step.dependOn(&binary.step);

        const library = b.addInstallDirectory(.{
            .source_dir = b.path("lib"),
            .install_dir = .{ .custom = tree },
            .install_subdir = "lib",
        });
        release_step.dependOn(&library.step);

        for (release_docs) |doc| {
            const copied = b.addInstallFile(b.path(doc), b.fmt("{s}/{s}", .{ tree, doc }));
            release_step.dependOn(&copied.step);
        }
    }
}

fn addPhi(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    options: *std.Build.Step.Options,
) *std.Build.Step.Compile {
    const build_options = options.createModule();
    const compiler = b.createModule(.{
        .root_source_file = b.path("compiler/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    const exe = b.addExecutable(.{
        .name = "phi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("tools/phi/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = compiler },
                .{ .name = "build_options", .module = build_options },
            },
        }),
    });
    exe.stack_size = analysis_stack_bytes;
    return exe;
}

/// A build on the manifest's tag is that release, others say which commit they are.
fn resolveVersion(b: *std.Build) []const u8 {
    const manifest = zon.version;
    // a tree with no history to read must not claim the release it precedes
    const unknown = b.fmt("{s}-dev", .{manifest});

    var code: u8 = undefined;
    const stdout = b.runAllowFail(&.{
        "git",                        "-C",
        b.build_root.path orelse ".", "describe",
        "--match",                    "*.*.*",
        "--tags",                     "--abbrev=9",
    }, &code, .ignore) catch return unknown;
    const described = std.mem.trim(u8, stdout, " \n\r");

    // no trailing distance means the commit carries the tag itself
    const dev = splitDescribe(described) orelse {
        if (std.mem.eql(u8, described, manifest)) return manifest;
        std.debug.panic(
            "tag '{s}' and build.zig.zon version '{s}' disagree",
            .{ described, manifest },
        );
    };

    // a tag at or past the manifest would number this build below a release
    const tagged = std.SemanticVersion.parse(dev.tag) catch
        std.debug.panic("tag '{s}' is not a version", .{dev.tag});
    const next = std.SemanticVersion.parse(manifest) catch
        std.debug.panic("build.zig.zon version '{s}' is not a version", .{manifest});
    if (tagged.order(next) != .lt) std.debug.panic(
        "tag '{s}' does not precede build.zig.zon version '{s}'",
        .{ dev.tag, manifest },
    );

    return b.fmt("{s}-dev.{s}+{s}", .{ manifest, dev.distance, dev.hash });
}

const Describe = struct { tag: []const u8, distance: []const u8, hash: []const u8 };

/// `0.1.0-47-g7f3a91c9a` is 47 commits past 0.1.0, the last two fields by shape.
fn splitDescribe(described: []const u8) ?Describe {
    const hash_dash = std.mem.lastIndexOfScalar(u8, described, '-') orelse return null;
    const hash = described[hash_dash + 1 ..];
    if (hash.len < 2 or hash[0] != 'g') return null;
    for (hash[1..]) |c| if (!std.ascii.isHex(c)) return null;

    const head = described[0..hash_dash];
    const distance_dash = std.mem.lastIndexOfScalar(u8, head, '-') orelse return null;
    const distance = head[distance_dash + 1 ..];
    if (distance.len == 0) return null;
    for (distance) |c| if (!std.ascii.isDigit(c)) return null;

    return .{
        .tag = head[0..distance_dash],
        .distance = distance,
        .hash = hash[1..],
    };
}

fn addTestFiles(b: *std.Build, run: *std.Build.Step.Run) void {
    run.setCwd(b.path("."));
    run.addArg("test");
}

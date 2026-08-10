//! The root object.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Diagnostic = @import("Diagnostic.zig");
const IR = @import("IR.zig");
const Layout = @import("Layout.zig");
const Module = @import("Module.zig");
const Pool = @import("Pool.zig");
const Source = @import("Source.zig");
const Token = @import("Token.zig");
const spell = @import("util/spell.zig");

const Decl = Module.Decl;

// tables

gpa: Allocator,
io: std.Io,
pool: Pool,
/// Heap-stable, because analysis holds a module while loading others.
modules: std.ArrayList(*Module),
module_map: std.StringHashMapUnmanaged(Module.Index),
decls: std.ArrayList(Decl),
instances: std.ArrayList(Instance),
instance_args: std.ArrayList(Pool.Index),
instance_map: std.HashMapUnmanaged(
    Pool.Instance,
    void,
    InstanceIndexContext,
    std.hash_map.default_max_load_percentage,
),
/// Parameters and fields share one shape, so one table.
rows: std.ArrayList(Row),
/// Marked and restored, because one signature can demand another.
rows_scratch: std.ArrayList(Row),
/// Bodies never nest, so one builder serves them all.
body_builder: Check.Builder,
/// Staged literal parts and call arguments, marked and restored.
operands: std.ArrayList(Check.Operand),
body_queue: std.ArrayList(Pool.Instance),
funcs: std.ArrayList(IR.Func),
/// Every function's instructions, blocks, and extra words, which each `Func` ranges into.
insts: IR.InstList,
inst_extra: std.ArrayList(u32),
blocks: std.ArrayList(IR.Block),
diagnostics: std.ArrayList(Entry),
/// One row per (module, code, anchor), so re-walked code reports once.
reported: std.AutoHashMapUnmanaged(ReportKey, void),
/// Each checked expression's type, recorded only when the host asked.
expr_types: std.AutoHashMapUnmanaged(ExprKey, Pool.Index),
/// Every layout ever computed, so a type's is computed once.
layouts: std.AutoHashMapUnmanaged(Pool.Index, Layout),
/// `std.prelude`, when it loaded.
prelude: ?Module.Index,

// transient analysis state

/// What is being analyzed, for cycle reports.
stack: std.ArrayList(Frame),
/// Backs diagnostic text, module keys, and paths until deinit.
arena: std.heap.ArenaAllocator,

// configuration

loader: Loader,
/// Directory of the root file. Bare module paths resolve against it.
root_dir: []const u8,
/// Stem of the root file, its name if something imports it back.
root_stem: []const u8,
/// Where `std.` resolves, or null.
std_dir: ?[]const u8,
/// Whether checking records every expression's type for `exprType`.
record_expr_types: bool,

const Compilation = @This();

pub const instantiate_max = 64;
pub const analyze_max = 128;
const diagnostics_max = 256;

/// A declaration plus its bracket arguments, memoized so identity is the row.
pub const Instance = struct {
    decl: Decl.Index,
    args: Range,
    /// A struct type, or a function return type once resolved.
    type: Pool.Index,
    /// Fields for a struct, parameters for a function.
    rows: Range,
    /// Where this instance was first demanded.
    origin: Origin,
    /// The instance whose checking first demanded this one.
    parent: Pool.OptionalInstance,
    /// Generic ancestors, this instance included.
    depth: u32,
    /// Row in `funcs` once the body committed.
    func: IR.Func.OptionalIndex,
    /// Fields resolved, or signature resolved.
    rows_state: Decl.State,
    /// The embedding walk, or the body check.
    deep_state: Decl.State,
};

/// The one loading seam. A host replaces it to serve unsaved editor buffers.
pub const Loader = struct {
    context: ?*anyopaque,
    load: *const fn (
        context: ?*anyopaque,
        gpa: Allocator,
        io: std.Io,
        path: []const u8,
    ) Source.LoadError!Source,

    pub const disk: Loader = .{ .context = null, .load = loadFromDisk };

    fn loadFromDisk(
        context: ?*anyopaque,
        gpa: Allocator,
        io: std.Io,
        path: []const u8,
    ) Source.LoadError!Source {
        assert(context == null);
        assert(path.len > 0);
        return Source.load(gpa, io, .cwd(), path);
    }
};

pub const Range = struct {
    start: u32,
    len: u32,

    pub const empty: Range = .{ .start = 0, .len = 0 };

    pub fn end(range: Range) u32 {
        return range.start + range.len;
    }

    pub fn at(range: Range, position: u32) u32 {
        assert(position < range.len);
        return range.start + position;
    }
};

/// A parameter or a field.
pub const Row = struct {
    name: Pool.String,
    type: Pool.Index,
    node: AST.Node.Index,

    pub const Index = enum(u32) {
        _,

        pub fn from(raw: usize) Index {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Index) u32 {
            return @intFromEnum(index);
        }
    };
};

/// One memoized computation, runnable only through `ensure`.
pub const Unit = struct {
    kind: Kind,
    index: u32,

    pub const Kind = enum(u8) { decl, rows, alias, embedding, signature, body };

    pub fn forDecl(index: Decl.Index) Unit {
        return .{ .kind = .decl, .index = index.int() };
    }

    pub fn of(kind: Kind, instance: Pool.Instance) Unit {
        assert(kind != .decl);
        return .{ .kind = kind, .index = instance.int() };
    }

    fn eql(unit: Unit, other: Unit) bool {
        if (unit.kind != other.kind) return false;
        return unit.index == other.index;
    }
};

/// Where a demand came from, named by a cycle report or the trail.
pub const Origin = struct { module: Module.Index, node: AST.Node.Index };

const Frame = struct { unit: Unit, origin: Origin };

/// A report names a node or a token, never an offset that shifts under edits.
const ReportAnchor = enum(u8) { node, token };

const ReportKey = struct {
    module: Module.Index,
    code: Diagnostic.Code,
    anchor: u32,
    anchor_kind: ReportAnchor,
};

const ExprKey = struct { instance: Pool.Instance, node: AST.Node.Index };

/// A diagnostic and the unit that produced it. Null belongs to parsing and registration.
pub const Entry = struct {
    module: Module.Index,
    unit: ?Unit,
    diagnostic: Diagnostic,
};

pub const Options = struct {
    root_path: []const u8,
    std_dir: ?[]const u8,
    /// An editor host records every expression's type. A batch compile leaves it off.
    record_expr_types: bool = false,
    loader: Loader = .disk,
};

pub fn init(comp: *Compilation, gpa: Allocator, io: std.Io, options: Options) Allocator.Error!void {
    assert(options.root_path.len > 0);

    comp.* = .{
        .gpa = gpa,
        .io = io,
        .pool = undefined,
        .modules = .empty,
        .module_map = .empty,
        .decls = .empty,
        .instances = .empty,
        .instance_args = .empty,
        .instance_map = .empty,
        .rows = .empty,
        .rows_scratch = .empty,
        .body_builder = .empty,
        .operands = .empty,
        .body_queue = .empty,
        .funcs = .empty,
        .insts = .empty,
        .inst_extra = .empty,
        .blocks = .empty,
        .diagnostics = .empty,
        .reported = .empty,
        .expr_types = .empty,
        .layouts = .empty,
        .prelude = null,
        .stack = .empty,
        .arena = .init(gpa),
        .loader = options.loader,
        .root_dir = std.fs.path.dirname(options.root_path) orelse ".",
        .root_stem = std.fs.path.stem(options.root_path),
        .std_dir = options.std_dir,
        .record_expr_types = options.record_expr_types,
    };

    // `analyze_max` caps the stack, so one reservation serves forever
    try comp.stack.ensureTotalCapacity(gpa, analyze_max);
    errdefer comp.stack.deinit(gpa);

    try comp.pool.init(gpa);
}

pub fn deinit(comp: *Compilation) void {
    const gpa = comp.gpa;

    for (comp.modules.items) |module| {
        module.deinit(gpa);
        gpa.destroy(module);
    }
    comp.modules.deinit(gpa);
    comp.module_map.deinit(gpa);

    comp.funcs.deinit(gpa);
    comp.insts.deinit(gpa);
    comp.inst_extra.deinit(gpa);
    comp.blocks.deinit(gpa);

    comp.body_builder.deinit(gpa);
    comp.operands.deinit(gpa);
    comp.body_queue.deinit(gpa);
    comp.pool.deinit(gpa);
    comp.decls.deinit(gpa);
    comp.instances.deinit(gpa);
    comp.instance_args.deinit(gpa);
    comp.instance_map.deinit(gpa);
    comp.rows.deinit(gpa);
    comp.rows_scratch.deinit(gpa);
    comp.diagnostics.deinit(gpa);
    comp.reported.deinit(gpa);
    comp.expr_types.deinit(gpa);
    comp.layouts.deinit(gpa);
    comp.stack.deinit(gpa);
    comp.arena.deinit();
    comp.* = undefined;
}

// the driver

/// Check one program from its root file, whose source this takes over.
pub fn compile(comp: *Compilation, root_source: Source) Allocator.Error!void {
    assert(comp.modules.items.len == 0);

    const in_std = comp.std_dir != null and pathInside(comp.std_dir.?, comp.root_dir);
    const space: Module.Space = if (in_std) .std else .root;
    const key = try comp.fmt("{t}:{s}", .{ space, comp.root_stem });

    const index = try Module.register(comp, key, space, root_source);
    assert(index == .root);
    const module = comp.moduleAt(index);

    comp.prelude = switch (try Module.loadModule(comp, .std, Module.prelude_name)) {
        .module => |found| found,
        .not_found, .no_std => null,
    };

    for (module.decls.start..module.decls.end()) |raw| {
        const decl_index: Decl.Index = .from(raw);
        const decl = comp.declAt(decl_index);
        if (decl.owner != .none) continue;

        const origin: Origin = .{ .module = index, .node = decl.node };
        try comp.ensure(.forDecl(decl_index), origin);
        try comp.enqueueBodies(decl_index, origin);
    }
    try comp.drainBodies();
    assert(comp.stack.items.len == 0);
}

/// A plain function, and the plain methods of a plain struct.
fn enqueueBodies(comp: *Compilation, decl_index: Decl.Index, origin: Origin) Allocator.Error!void {
    const decl = comp.declAt(decl_index);
    switch (decl.kind) {
        .import, .type_alias, .unit_decl, .let => {},
        .fn_decl => try comp.enqueueBodiesFn(decl_index, origin),
        .struct_decl => {
            if (decl.state != .done) return;
            if (comp.isGeneric(decl_index)) return;
            const members = decl.members();
            for (members.start..members.start + members.len) |raw| {
                const member: Decl.Index = .from(raw);
                try comp.enqueueBodiesFn(member, origin);
            }
        },
    }
}

fn enqueueBodiesFn(
    comp: *Compilation,
    decl_index: Decl.Index,
    origin: Origin,
) Allocator.Error!void {
    const decl = comp.declAt(decl_index);
    if (decl.kind != .fn_decl) return;
    if (decl.state == .poisoned) return;
    if (comp.isGeneric(decl_index)) return;

    try comp.enqueueBody(try comp.instantiate(decl_index, &.{}, origin));
}

/// The drain's `ensure` makes a duplicate enqueue a no-op.
pub fn enqueueBody(comp: *Compilation, instance: Pool.Instance) Allocator.Error!void {
    assert(comp.declAt(comp.instanceDecl(instance)).kind == .fn_decl);
    if (comp.instanceAt(instance).deep_state != .unanalyzed) return;
    try comp.body_queue.append(comp.gpa, instance);
}

/// Draining enqueues more, and stops because `ensure` runs each instance once.
fn drainBodies(comp: *Compilation) Allocator.Error!void {
    var next: usize = 0;
    while (next < comp.body_queue.items.len) : (next += 1) {
        const instance = comp.body_queue.items[next];
        const origin = comp.instanceAt(instance).origin;
        try comp.ensure(.of(.signature, instance), origin);
        try comp.ensure(.of(.body, instance), origin);
    }
    comp.body_queue.clearRetainingCapacity();
}

/// Whether a declaration only means something once instantiated.
pub fn isGeneric(comp: *const Compilation, decl_index: Decl.Index) bool {
    const decl = comp.declAt(decl_index);
    if (comp.typeParamCount(decl_index) > 0) return true;
    if (decl.owner.unwrap()) |owner| return comp.isGeneric(owner);
    return false;
}

// ensure, the one door into every memoized computation

pub fn ensure(comp: *Compilation, unit: Unit, origin: Origin) Allocator.Error!void {
    switch (comp.unitState(unit)) {
        .done, .poisoned => return,
        .in_progress => return comp.reportCycle(unit, origin),
        .unanalyzed => {},
    }

    // analysis recurses through whatever it demands
    if (comp.stack.items.len >= analyze_max) {
        try comp.reportNode(origin.module, origin.node, .{
            .code = .analysis_too_deep,
            .message = try comp.fmt(
                "checking this follows a chain more than {d} declarations deep",
                .{analyze_max},
            ),
            .label = "the chain stops here",
            .help = "a definition this far down a dependency chain is past what " ++
                "the compiler follows",
        });
        comp.setUnitState(unit, .poisoned);
        return;
    }

    // only bracket arguments count against the instantiation limit
    if (unit.kind != .decl) {
        const depth = comp.instanceAt(@enumFromInt(unit.index)).depth;
        if (depth > instantiate_max) {
            try comp.reportNode(origin.module, origin.node, .{
                .code = .instantiates_too_deep,
                .message = try comp.fmt("this instantiates more than {d} levels deep", .{
                    instantiate_max,
                }),
                .label = "the limit is here",
                .help = "a type or function that instantiates itself never bottoms out",
            });
            comp.setUnitState(unit, .poisoned);
            return;
        }
    }

    comp.setUnitState(unit, .in_progress);
    // `init` reserved `analyze_max`, which the depth check above holds it under
    assert(comp.stack.items.len < analyze_max);
    comp.stack.appendAssumeCapacity(.{ .unit = unit, .origin = origin });
    defer _ = comp.stack.pop();

    const ok = switch (unit.kind) {
        .decl => try comp.runDecl(@enumFromInt(unit.index)),
        .rows => try Check.structRows(comp, @enumFromInt(unit.index)),
        .alias => try Check.aliasInstance(comp, @enumFromInt(unit.index)),
        .embedding => try Check.structEmbedding(comp, @enumFromInt(unit.index)),
        .signature => try Check.fnSignature(comp, @enumFromInt(unit.index)),
        .body => try Check.fnBody(comp, @enumFromInt(unit.index)),
    };
    comp.setUnitState(unit, if (ok) .done else .poisoned);
}

fn runDecl(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    const decl = comp.declAt(decl_index);
    switch (decl.kind) {
        .import => return Module.resolveImport(comp, decl_index),
        .type_alias => {
            if (comp.isGeneric(decl_index)) return true;
            return Check.typeAlias(comp, decl_index);
        },
        .unit_decl => {
            _ = try comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
            return true;
        },
        .let => return Check.topLevelLet(comp, decl_index),
        .fn_decl => return true,
        .struct_decl => {
            if (comp.isGeneric(decl_index)) return true;
            const origin: Origin = .{ .module = decl.module, .node = decl.node };
            const instance = try comp.instantiate(decl_index, &.{}, origin);
            try comp.ensure(.of(.rows, instance), origin);
            try comp.ensure(.of(.embedding, instance), origin);
            return true;
        },
    }
}

fn unitState(comp: *const Compilation, unit: Unit) Decl.State {
    return switch (unit.kind) {
        .decl => comp.declAt(@enumFromInt(unit.index)).state,
        .rows, .alias, .signature => comp.instanceAt(@enumFromInt(unit.index)).rows_state,
        .embedding, .body => comp.instanceAt(@enumFromInt(unit.index)).deep_state,
    };
}

fn setUnitState(comp: *Compilation, unit: Unit, state: Decl.State) void {
    switch (unit.kind) {
        .decl => comp.declPtr(@enumFromInt(unit.index)).state = state,
        .rows, .alias, .signature => comp.instancePtr(@enumFromInt(unit.index)).rows_state = state,
        .embedding, .body => comp.instancePtr(@enumFromInt(unit.index)).deep_state = state,
    }
}

/// A re-entry is a cycle. The chain back becomes the notes.
fn reportCycle(comp: *Compilation, unit: Unit, origin: Origin) Allocator.Error!void {
    @branchHint(.cold);

    const name = try comp.unitName(unit);
    const message = switch (unit.kind) {
        .decl => switch (comp.declAt(@enumFromInt(unit.index)).kind) {
            .let => try comp.fmt("'{s}' takes its value from itself", .{name}),
            .type_alias => try comp.fmt("type '{s}' is an alias of itself", .{name}),
            .import => "this import goes in a circle",
            .struct_decl, .unit_decl, .fn_decl => "this definition goes in a circle",
        },
        .alias => try comp.fmt("type '{s}' is an alias of itself", .{name}),
        .embedding => try comp.fmt("'{s}' holds itself by value, so it has no size", .{name}),
        .rows, .signature, .body => "this definition goes in a circle",
    };
    const help: ?[]const u8 = switch (unit.kind) {
        .embedding => try comp.fmt("break the cycle with a pointer: '*{s}' or '*{s} | none'", .{
            name, name,
        }),
        else => null,
    };

    // the frames above this unit are the chain back to it
    var position: usize = comp.stack.items.len;
    for (comp.stack.items, 0..) |frame, at| {
        if (frame.unit.eql(unit)) {
            position = at;
            break;
        }
    }
    assert(position < comp.stack.items.len);

    var chain: std.ArrayList(Diagnostic.Note) = .empty;
    defer chain.deinit(comp.gpa);
    for (comp.stack.items[position + 1 ..]) |frame| {
        try chain.append(comp.gpa, comp.noteAt(
            frame.origin.module,
            frame.origin.node,
            try comp.fmt("which needs '{s}' here", .{try comp.unitName(frame.unit)}),
        ));
    }

    try comp.reportNode(origin.module, origin.node, .{
        .code = if (unit.kind == .embedding) .size_cycle else .value_cycle,
        .message = message,
        .label = "the circle closes here",
        .help = help,
        .notes = try comp.notes(chain.items),
    });
}

fn unitName(comp: *Compilation, unit: Unit) Allocator.Error![]const u8 {
    switch (unit.kind) {
        .decl => {
            const decl = comp.declAt(@enumFromInt(unit.index));
            return comp.pool.stringText(decl.name);
        },
        else => return comp.instanceName(@enumFromInt(unit.index)),
    }
}

// instantiation, where one memo table makes identity the row

pub fn instantiate(
    comp: *Compilation,
    decl_index: Decl.Index,
    args: []const Pool.Index,
    origin: Origin,
) Allocator.Error!Pool.Instance {
    assert(comp.declAt(decl_index).kind == .struct_decl or
        comp.declAt(decl_index).kind == .fn_decl or
        comp.declAt(decl_index).kind == .type_alias);

    if (args.len == 0) {
        if (comp.declAt(decl_index).plain_instance.unwrap()) |instance| return instance;
        const index = try comp.newInstance(decl_index, args, origin);
        comp.declPtr(decl_index).plain_instance = index.toOptional();
        return index;
    }

    const gop = try comp.instance_map.getOrPutContextAdapted(
        comp.gpa,
        InstanceKey{ .decl = decl_index, .args = args },
        InstanceKeyAdapter{ .comp = comp },
        InstanceIndexContext{ .comp = comp },
    );
    if (gop.found_existing) return gop.key_ptr.*;

    const index = try comp.newInstance(decl_index, args, origin);
    gop.key_ptr.* = index;
    return index;
}

fn newInstance(
    comp: *Compilation,
    decl_index: Decl.Index,
    args: []const Pool.Index,
    origin: Origin,
) Allocator.Error!Pool.Instance {
    if (comp.instances.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: Pool.Instance = .from(comp.instances.items.len);

    const parent: Pool.OptionalInstance = parent: {
        const unit = comp.currentUnit() orelse break :parent .none;
        if (unit.kind == .decl) break :parent .none;
        break :parent @enumFromInt(unit.index);
    };
    var depth: u32 = @intFromBool(args.len > 0);
    if (parent.unwrap()) |above| depth += comp.instanceAt(above).depth;

    const args_start: u32 = @intCast(comp.instance_args.items.len);
    try comp.instance_args.appendSlice(comp.gpa, args);
    try comp.instances.append(comp.gpa, .{
        .decl = decl_index,
        .args = .{ .start = args_start, .len = @intCast(args.len) },
        .type = .poison,
        .rows = .empty,
        .origin = origin,
        .parent = parent,
        .depth = depth,
        .func = .none,
        .rows_state = .unanalyzed,
        .deep_state = .unanalyzed,
    });

    // a type the moment it exists, so a struct can name itself
    if (comp.declAt(decl_index).kind == .struct_decl) {
        comp.instancePtr(index).type = try comp.pool.intern(comp.gpa, .{
            .type_struct = index,
        });
    }
    return index;
}

pub fn declAt(comp: *const Compilation, index: Decl.Index) Decl {
    assert(index.int() < comp.decls.items.len);
    return comp.decls.items[index.int()];
}

pub fn declPtr(comp: *Compilation, index: Decl.Index) *Decl {
    assert(index.int() < comp.decls.items.len);
    return &comp.decls.items[index.int()];
}

pub fn instanceAt(comp: *const Compilation, index: Pool.Instance) Instance {
    assert(index.int() < comp.instances.items.len);
    return comp.instances.items[index.int()];
}

pub fn instancePtr(comp: *Compilation, index: Pool.Instance) *Instance {
    assert(index.int() < comp.instances.items.len);
    return &comp.instances.items[index.int()];
}

pub fn moduleAt(comp: *const Compilation, index: Module.Index) *Module {
    assert(index.int() < comp.modules.items.len);
    return comp.modules.items[index.int()];
}

pub fn treeOf(comp: *const Compilation, index: Module.Index) *const AST {
    return &comp.moduleAt(index).tree;
}

pub fn rowAt(comp: *const Compilation, index: Row.Index) Row {
    assert(index.int() < comp.rows.items.len);
    return comp.rows.items[index.int()];
}

pub fn funcAt(comp: *const Compilation, index: IR.Func.Index) IR.Func {
    assert(index.int() < comp.funcs.items.len);
    return comp.funcs.items[index.int()];
}

/// The declaration rows a range names, a module's usually.
pub fn declsIn(comp: *const Compilation, range: Range) []const Decl {
    assert(range.end() <= comp.decls.items.len);
    return comp.decls.items[range.start..range.end()];
}

pub fn hasErrors(comp: *const Compilation) bool {
    return comp.diagnostics.items.len > 0;
}

pub fn instanceDecl(comp: *const Compilation, index: Pool.Instance) Decl.Index {
    return comp.instanceAt(index).decl;
}

/// A struct's type, or a resolved return type.
pub fn instanceType(comp: *const Compilation, index: Pool.Instance) Pool.Index {
    return comp.instanceAt(index).type;
}

pub fn ensureRows(comp: *Compilation, index: Pool.Instance) Allocator.Error!void {
    const decl = comp.declAt(comp.instanceDecl(index));
    try comp.ensure(.of(.rows, index), .{ .module = decl.module, .node = decl.node });
}

/// Invalidated by any other instantiation.
pub fn instanceArgs(comp: *const Compilation, index: Pool.Instance) []const Pool.Index {
    const instance = comp.instanceAt(index);
    return comp.instance_args.items[instance.args.start..][0..instance.args.len];
}

/// Fields, or signature parameters. Invalidated by any other commit.
pub fn instanceRows(comp: *const Compilation, index: Pool.Instance) []const Row {
    const instance = comp.instanceAt(index);
    return comp.rows.items[instance.rows.start..][0..instance.rows.len];
}

pub fn funcBlocks(comp: *const Compilation, func: IR.Func) []const IR.Block {
    return comp.blocks.items[func.blocks.start..][0..func.blocks.len];
}

pub fn funcExtra(comp: *const Compilation, func: IR.Func) []const u32 {
    return comp.inst_extra.items[func.extra.start..][0..func.extra.len];
}

pub fn instAt(comp: *const Compilation, at: u32) IR.Inst {
    assert(at < comp.insts.len);
    return comp.insts.get(at);
}

pub fn rememberExprType(
    comp: *Compilation,
    instance: Pool.Instance,
    node: AST.Node.Index,
    type_index: Pool.Index,
) Allocator.Error!void {
    assert(comp.record_expr_types);
    assert(comp.pool.isType(type_index));
    try comp.expr_types.put(comp.gpa, .{ .instance = instance, .node = node }, type_index);
}

/// The type checking decided, the editor's question answered from data.
pub fn exprType(
    comp: *const Compilation,
    instance: Pool.Instance,
    node: AST.Node.Index,
) ?Pool.Index {
    assert(instance.int() < comp.instances.items.len);
    return comp.expr_types.get(.{ .instance = instance, .node = node });
}

const InstanceKey = struct { decl: Decl.Index, args: []const Pool.Index };

const InstanceKeyAdapter = struct {
    comp: *const Compilation,

    pub fn hash(_: InstanceKeyAdapter, key: InstanceKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&key.decl));
        hasher.update(std.mem.sliceAsBytes(key.args));
        return hasher.final();
    }

    pub fn eql(adapter: InstanceKeyAdapter, key: InstanceKey, index: Pool.Instance) bool {
        const instance = adapter.comp.instanceAt(index);
        if (instance.decl != key.decl) return false;
        return std.mem.eql(Pool.Index, key.args, adapter.comp.instanceArgs(index));
    }
};

const InstanceIndexContext = struct {
    comp: *const Compilation,

    pub fn hash(context: InstanceIndexContext, index: Pool.Instance) u64 {
        const instance = context.comp.instanceAt(index);
        return (InstanceKeyAdapter{ .comp = context.comp }).hash(.{
            .decl = instance.decl,
            .args = context.comp.instanceArgs(index),
        });
    }

    pub fn eql(_: InstanceIndexContext, a: Pool.Instance, b: Pool.Instance) bool {
        return a == b;
    }
};

pub const Report = struct {
    code: Diagnostic.Code,
    message: []const u8,
    label: []const u8 = "",
    help: ?[]const u8 = null,
    notes: []const Diagnostic.Note = &.{},
};

pub fn reportNode(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
    report_value: Report,
) Allocator.Error!void {
    @branchHint(.cold);
    const tree = comp.treeOf(module);
    try comp.report(module, node.int(), .node, tree.nodeSpan(node), report_value);
}

pub fn reportToken(
    comp: *Compilation,
    module: Module.Index,
    token: Token.Index,
    report_value: Report,
) Allocator.Error!void {
    @branchHint(.cold);
    const tree = comp.treeOf(module);
    try comp.report(module, token.int(), .token, .{
        .start = tree.tokenStart(token),
        .end = tree.tokenEnd(token),
    }, report_value);
}

fn report(
    comp: *Compilation,
    module: Module.Index,
    anchor: u32,
    anchor_kind: ReportAnchor,
    span: Diagnostic.Span,
    report_value: Report,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(report_value.message.len > 0);
    assert(span.start <= span.end);

    // one mistake, one report, however often the spot is re-walked
    const key: ReportKey = .{
        .module = module,
        .code = report_value.code,
        .anchor = anchor,
        .anchor_kind = anchor_kind,
    };
    const seen = try comp.reported.getOrPut(comp.gpa, key);
    if (seen.found_existing) return;
    if (comp.diagnostics.items.len >= diagnostics_max) return;

    try comp.diagnostics.append(comp.gpa, .{
        .module = module,
        .unit = comp.currentUnit(),
        .diagnostic = .{
            .code = report_value.code,
            .span = span,
            .message = report_value.message,
            .label = report_value.label,
            .help = report_value.help,
            .notes = try comp.withTrail(report_value.notes),
        },
    });
}

/// The unit being run owns what it reports. Null before any unit runs.
fn currentUnit(comp: *const Compilation) ?Unit {
    if (comp.stack.items.len == 0) return null;
    return comp.stack.items[comp.stack.items.len - 1].unit;
}

/// The parser budgets and orders its own reports, so nothing is deduplicated here.
pub fn adoptParseErrors(
    comp: *Compilation,
    module: Module.Index,
    errors: []const Diagnostic,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(errors.len > 0);

    for (errors) |diagnostic| {
        if (comp.diagnostics.items.len >= diagnostics_max) return;
        try comp.diagnostics.append(comp.gpa, .{
            .module = module,
            .unit = null,
            .diagnostic = diagnostic,
        });
    }
}

/// Appended to every report, innermost instance first.
fn withTrail(
    comp: *Compilation,
    notes_in: []const Diagnostic.Note,
) Allocator.Error![]Diagnostic.Note {
    const trail_cap = 8;

    var shown: [trail_cap]Pool.Instance = undefined;
    var generic_count: u32 = 0;
    var current: Pool.OptionalInstance = current: {
        const unit = comp.currentUnit() orelse break :current .none;
        if (unit.kind == .decl) break :current .none;
        break :current @enumFromInt(unit.index);
    };
    while (current.unwrap()) |instance| {
        const row = comp.instanceAt(instance);
        if (row.args.len > 0) {
            if (generic_count < trail_cap) shown[generic_count] = instance;
            generic_count += 1;
        }
        // a parent is created before its child, so the walk must descend
        if (row.parent.unwrap()) |above| assert(above.int() < instance.int());
        current = row.parent;
    }

    const shown_count = @min(generic_count, trail_cap);
    const extra: u32 = if (generic_count > trail_cap) 1 else 0;
    const total = notes_in.len + shown_count + extra;
    if (total == 0) return &.{};

    const out = try comp.arena.allocator().alloc(Diagnostic.Note, total);
    @memcpy(out[0..notes_in.len], notes_in);

    for (shown[0..shown_count], notes_in.len..) |instance, at| {
        const origin = comp.instanceAt(instance).origin;
        out[at] = comp.noteAt(
            origin.module,
            origin.node,
            try comp.fmt("while checking '{s}', needed here", .{
                try comp.instanceName(instance),
            }),
        );
    }
    if (extra == 1) {
        out[total - 1] = .{ .message = try comp.fmt("and {d} more instantiation levels", .{
            generic_count - trail_cap,
        }) };
    }
    return out;
}

pub fn noteAt(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
    message: []const u8,
) Diagnostic.Note {
    const owner = comp.moduleAt(module);
    return .{
        .message = message,
        .span = owner.tree.nodeSpan(node),
        .source = &owner.source,
    };
}

pub fn notes(comp: *Compilation, list: []const Diagnostic.Note) Allocator.Error![]Diagnostic.Note {
    return comp.arena.allocator().dupe(Diagnostic.Note, list);
}

pub fn fmt(
    comp: *Compilation,
    comptime template: []const u8,
    args: anytype,
) Allocator.Error![]const u8 {
    comptime assert(template.len > 0);
    return std.fmt.allocPrint(comp.arena.allocator(), template, args);
}

pub fn didYouMean(
    comp: *Compilation,
    closest: spell.Closest,
) Allocator.Error!?[]const u8 {
    const found = closest.best orelse return null;
    return try comp.fmt("did you mean '{s}'?", .{found});
}

pub fn renderAll(comp: *Compilation, writer: *Writer, color: Diagnostic.Color) !void {
    assert(comp.diagnostics.items.len > 0);
    std.sort.insertion(Entry, comp.diagnostics.items, {}, entryBefore);
    for (comp.diagnostics.items) |entry| {
        const module = comp.moduleAt(entry.module);
        try entry.diagnostic.render(comp.gpa, &module.source, writer, color);
    }
}

fn entryBefore(_: void, entry: Entry, other: Entry) bool {
    if (entry.module != other.module) return entry.module.int() < other.module.int();
    return entry.diagnostic.span.start < other.diagnostic.span.start;
}

pub fn dumpIR(comp: *const Compilation, writer: *Writer) Writer.Error!void {
    var printed = false;
    for (comp.instances.items) |instance| {
        const index = instance.func.unwrap() orelse continue;
        if (printed) try writer.writeByte('\n');
        printed = true;
        try spell.writeFunc(comp, comp.funcAt(index), writer);
    }
}

/// One of the `spell` writers into the diagnostic arena.
fn spelled(comp: *Compilation, writer: anytype, subject: anytype) Allocator.Error![]const u8 {
    var out: Writer.Allocating = .init(comp.arena.allocator());
    writer(comp, &out.writer, subject) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
    };
    return out.written();
}

pub fn typeName(comp: *Compilation, index: Pool.Index) Allocator.Error![]const u8 {
    return comp.spelled(spell.writeType, index);
}

pub fn instanceName(comp: *Compilation, index: Pool.Instance) Allocator.Error![]const u8 {
    return comp.spelled(spell.writeInstance, index);
}

/// The value alone, for a message naming what did not fit.
pub fn spellValue(comp: *Compilation, value: Pool.Index) Allocator.Error![]const u8 {
    return comp.spelled(spell.writeConstantBare, value);
}

pub fn rowName(comp: *const Compilation, index: Row.Index) []const u8 {
    return comp.pool.stringText(comp.rowAt(index).name);
}

pub fn typeParamCount(comp: *const Compilation, decl_index: Decl.Index) u32 {
    return comp.declAt(decl_index).type_params;
}

/// Textual, which is enough to notice a root file inside the standard library.
fn pathInside(outer: []const u8, inner: []const u8) bool {
    const trimmed = std.mem.trimEnd(u8, outer, "/");
    if (std.mem.startsWith(u8, inner, trimmed) == false) return false;
    if (inner.len == trimmed.len) return true;
    return inner[trimmed.len] == '/';
}

// testing

const testing = std.testing;

/// One compilation over one file, which every test below stands up the same way.
fn testInit(comp: *Compilation, gpa: Allocator) Allocator.Error!void {
    try comp.init(gpa, testing.io, .{ .root_path = "test.phi", .std_dir = null });
}

fn testSource(gpa: Allocator, text: []const u8) Allocator.Error!Source {
    const buffer = try gpa.alloc(u8, text.len + Source.padding);
    @memcpy(buffer[0..text.len], text);
    buffer[text.len] = 0;
    return .{ .path = "test.phi", .bytes = buffer[0..text.len :0] };
}

test "instantiation identity is index equality" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\pub type Box[T] = {
        \\    item: T
        \\}
        \\pub type Boxed = Box[i64]
        \\fn hold(a: Box[i64], b: Boxed, c: Box[u8]) Boxed {
        \\    return a
        \\}
        \\
    ));
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const hold = comp.moduleAt(.root).findDecl("hold").?;
    const instance = try comp.instantiate(hold, &.{}, .{
        .module = .root,
        .node = comp.declAt(hold).node,
    });
    const rows = comp.instanceRows(instance);
    try testing.expectEqual(3, rows.len);

    // `Box[i64]` twice, and once through an alias, is one index
    try testing.expectEqual(rows[0].type, rows[1].type);
    try testing.expectEqual(rows[1].type, comp.instanceType(instance));
    // `Box[u8]` is another type entirely
    try testing.expect(rows[0].type != rows[2].type);
}

test "a generic alias is the type it names, not a new one" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    // `return b` compiles only because the alias and the union are one type
    try comp.compile(try testSource(gpa,
        \\type none
        \\type Maybe[T] = T | none
        \\fn pick(a: Maybe[i64], b: i64 | none) Maybe[i64] {
        \\    _ = a
        \\    return b
        \\}
        \\
    ));
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const pick = comp.moduleAt(.root).findDecl("pick").?;
    const instance = try comp.instantiate(pick, &.{}, .{
        .module = .root,
        .node = comp.declAt(pick).node,
    });
    const rows = comp.instanceRows(instance);
    try testing.expectEqual(2, rows.len);
    try testing.expectEqual(rows[0].type, rows[1].type);
    try testing.expectEqual(rows[0].type, comp.instanceType(instance));
}

test "a call chain compiles at any depth" {
    const gpa = testing.allocator;

    // far past `analyze_max`, which bodies do not count against
    const levels = 1000;

    var deep: Writer.Allocating = .init(gpa);
    defer deep.deinit();
    for (0..levels) |level| {
        try deep.writer.print("fn g{d}(n: i64) i64 {{ return g{d}(n) }}\n", .{
            level, level + 1,
        });
    }
    try deep.writer.print("fn g{d}(n: i64) i64 {{ return n }}\n", .{levels});

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();
    try comp.compile(try testSource(gpa, deep.written()));
    try testing.expectEqual(0, comp.diagnostics.items.len);
    try testing.expectEqual(levels + 1, comp.funcs.items.len);
}

test "the deepest nesting that reaches analysis does not overflow the stack" {
    const gpa = testing.allocator;

    const levels = analyze_max - 1;
    const nesting = 100;

    var deep: Writer.Allocating = .init(gpa);
    defer deep.deinit();
    for (0..levels) |level| {
        try deep.writer.print("fn g{d}(n: i64) i64 {{ return ", .{level});
        var call_buffer: [16]u8 = undefined;
        const call = try std.fmt.bufPrint(&call_buffer, "g{d}(", .{level + 1});
        try deep.writer.splatBytesAll(call, nesting);
        try deep.writer.writeAll("n");
        try deep.writer.splatBytesAll(")", nesting);
        try deep.writer.writeAll(" }\n");
    }
    try deep.writer.print("fn g{d}(n: i64) i64 {{ return n }}\n", .{levels});

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();
    try comp.compile(try testSource(gpa, deep.written()));
    try testing.expectEqual(0, comp.diagnostics.items.len);
}

test "one constant view is one entry, however often it is written" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\fn here() []u32 {
        \\    return [2, 3, 5, 7]
        \\}
        \\fn there() []u32 {
        \\    return [2, 3, 5, 7]
        \\}
        \\
    ));
    try testing.expectEqual(0, comp.diagnostics.items.len);
    try testing.expectEqual(2, comp.funcs.items.len);

    // interning is what shares the bytes, so the two sites return one constant
    const here = comp.funcBlocks(comp.funcAt(.from(0)))[0].terminator.ret;
    const there = comp.funcBlocks(comp.funcAt(.from(1)))[0].terminator.ret;
    try testing.expectEqual(here, there);

    const viewed = comp.pool.keyOf(here.unwrap().constant).value_slice;
    try testing.expectEqual(4, comp.pool.aggregateLen(viewed.data));
}

test "a diagnostic renders across files" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\fn f() i64 {
        \\    return missing
        \\}
        \\
    ));
    try testing.expectEqual(1, comp.diagnostics.items.len);

    var out: Writer.Allocating = .init(gpa);
    defer out.deinit();
    try comp.renderAll(&out.writer, .off);
    try testing.expect(std.mem.indexOf(u8, out.written(), "nothing named 'missing'") != null);
}

test "a diagnostic names the unit that produced it" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\fn f() i64 {
        \\    return missing
        \\}
        \\
    ));
    try testing.expectEqual(1, comp.diagnostics.items.len);

    const entry = comp.diagnostics.items[0];
    try testing.expect(entry.unit != null);
    try testing.expectEqual(Unit.Kind.body, entry.unit.?.kind);
}

test "a program built without the standard library says where std would be" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa, "import std.mem\n"));

    var out: Writer.Allocating = .init(gpa);
    defer out.deinit();
    try comp.renderAll(&out.writer, .off);
    try testing.expect(std.mem.indexOf(
        u8,
        out.written(),
        "the standard library was not found",
    ) != null);
}

test "a file with a parse error is still checked" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try testInit(&comp, gpa);
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\fn broken( {
        \\}
        \\
        \\fn ok() i64 {
        \\    return missing
        \\}
        \\
    ));
    try testing.expectEqual(2, comp.diagnostics.items.len);

    const parse_entry = comp.diagnostics.items[0];
    try testing.expectEqual(Diagnostic.Code.expected_token, parse_entry.diagnostic.code);
    try testing.expectEqual(null, parse_entry.unit);

    const analysis_entry = comp.diagnostics.items[1];
    try testing.expectEqual(Diagnostic.Code.undefined_name, analysis_entry.diagnostic.code);
    try testing.expect(analysis_entry.unit != null);
}

test "the checker answers a type question as data" {
    const gpa = testing.allocator;

    var comp: Compilation = undefined;
    try comp.init(gpa, testing.io, .{
        .root_path = "test.phi",
        .std_dir = null,
        .record_expr_types = true,
    });
    defer comp.deinit();

    try comp.compile(try testSource(gpa,
        \\fn f(n: i64) i64 {
        \\    return n + 1
        \\}
        \\
    ));
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const f = comp.moduleAt(.root).findDecl("f").?;
    const instance = try comp.instantiate(f, &.{}, .{
        .module = .root,
        .node = comp.declAt(f).node,
    });

    const tree = comp.treeOf(.root);
    const decl_view = tree.viewOf(comp.declAt(f).node).fn_decl;
    const statements = tree.viewOf(decl_view.body).block;
    const returned = tree.viewOf(statements[0]).return_expr.unwrap().?;
    const sum = tree.viewOf(returned).binary;

    try testing.expectEqual(Pool.Index.i64_type, comp.exprType(instance, returned));
    try testing.expectEqual(Pool.Index.i64_type, comp.exprType(instance, sum.lhs));
}

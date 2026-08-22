const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Diagnostic = @import("Diagnostic.zig");
const Handle = @import("Handle.zig");
const IR = @import("IR.zig");
const Layout = @import("Layout.zig");
const Module = @import("Module.zig");
const Pool = @import("Pool.zig");
const Source = @import("Source.zig");
const Spell = @import("Spell.zig");
const Target = @import("Target.zig").Target;
const Token = @import("Token.zig");

const Decl = Module.Decl;

gpa: Allocator,
io: std.Io,
options: Options,
arena: std.heap.ArenaAllocator,

pool: Pool,
/// Heap-stable, analysis holds a module while loading others.
modules: std.ArrayList(*Module) = .empty,
module_map: std.StringHashMapUnmanaged(Module.Index) = .empty,
prelude: ?Module.Index = null,
decls: std.ArrayList(Decl) = .empty,
/// A bound per type parameter, `.poison` where there is none to enforce.
bounds: std.ArrayList(Pool.Index) = .empty,
instances: std.ArrayList(Instance) = .empty,
instance_map: ArgsMap(Decl.Index, Pool.Instance) = .empty,
/// Fields and parameters, one range per instance.
rows: std.ArrayList(Row) = .empty,
layouts: std.AutoHashMapUnmanaged(Pool.Index, Layout) = .empty,
/// What a call the compiler ran answered, per instance and arguments.
calls: ArgsMap(Pool.Instance, Pool.Index) = .empty,

/// The units in progress, innermost last.
stack: std.ArrayList(Frame) = .empty,
/// Bodies waiting to be checked, in the order the program reached them.
queue: std.ArrayList(Pool.Instance) = .empty,
scratch: Check.Scratch = .{},

ir: IR.Program = .{},
diagnostics: std.ArrayList(Entry) = .empty,
/// One row per (module, code, anchor), so re-walked code reports once.
reported: std.AutoHashMapUnmanaged(ReportKey, void) = .empty,

const Compilation = @This();

pub const instantiate_max = 64;
pub const analyze_max = 128;
const diagnostics_max = 256;

pub const Options = struct {
    root_path: []const u8,
    std_dir: ?[]const u8,
    target: Target = .host,
    loader: Loader = .disk,
};

/// The one loading seam. A host replaces it to serve unsaved buffers.
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

/// One declaration with one set of type arguments.
pub const Instance = struct {
    decl: Decl.Index,
    args: Range,
    /// The struct type, the alias target, or a function's return type.
    type: Pool.Index,
    rows: Range,
    origin: Origin,
    parent: Pool.OptionalInstance,
    /// How many generic instantiations stand above this one.
    depth: u32,
    func: IR.Func.OptionalIndex,
    /// Rows, an alias target, or a signature.
    head: Decl.State,
    /// A struct's embedding, or a function's body.
    body: Decl.State,
    queued: bool,
};

pub const Row = struct {
    name: Pool.String,
    type: Pool.Index,
    node: AST.Node.Index,

    pub const Index = Handle.Index("row");
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

    pub fn slice(range: Range, items: anytype) @TypeOf(items) {
        assert(range.end() <= items.len);
        return items[range.start..range.end()];
    }

    pub fn since(start: u32, len: usize) Range {
        assert(len >= start);
        return .{ .start = start, .len = @intCast(len - start) };
    }
};

/// One memoized computation, runnable only through `ensure`.
pub const Unit = union(enum) {
    decl: Decl.Index,
    head: Pool.Instance,
    body: Pool.Instance,
};

pub const Origin = struct { module: Module.Index, node: AST.Node.Index };

pub const Frame = struct { unit: Unit, origin: Origin };

/// A report names a node or a token, never an offset that edits shift.
pub const Anchor = union(enum) { node: AST.Node.Index, token: Token.Index };

const ReportKey = struct { module: Module.Index, code: Diagnostic.Code, anchor: Anchor };

pub const Entry = struct {
    module: Module.Index,
    unit: ?Unit,
    diagnostic: Diagnostic,
};

pub fn init(comp: *Compilation, gpa: Allocator, io: std.Io, options: Options) Allocator.Error!void {
    assert(options.root_path.len > 0);

    comp.* = .{ .gpa = gpa, .io = io, .options = options, .arena = .init(gpa), .pool = undefined };
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
    comp.decls.deinit(gpa);
    comp.bounds.deinit(gpa);
    comp.instances.deinit(gpa);
    comp.instance_map.deinit(gpa);
    comp.rows.deinit(gpa);
    comp.layouts.deinit(gpa);
    comp.calls.deinit(gpa);
    comp.stack.deinit(gpa);
    comp.queue.deinit(gpa);
    comp.scratch.deinit(gpa);
    comp.ir.deinit(gpa);
    comp.diagnostics.deinit(gpa);
    comp.reported.deinit(gpa);
    comp.pool.deinit(gpa);
    comp.arena.deinit();
    comp.* = undefined;
}

pub fn compile(comp: *Compilation, root_source: Source) Allocator.Error!void {
    assert(comp.modules.items.len == 0);

    const in_std = if (comp.options.std_dir) |dir| pathInside(dir, comp.rootDir()) else false;
    const space: Module.Space = if (in_std) .std else .root;
    const key = try comp.fmt("{t}:{s}", .{ space, std.fs.path.stem(comp.options.root_path) });

    const index = try Module.register(comp, key, space, root_source);
    assert(index == .root);
    comp.prelude = try Module.loadModule(comp, .std, Module.prelude_name);

    // the entry and everything it reaches is the program, the rest is checked for its report
    var program: []Pool.Instance = &.{};
    if (comp.entryDecl()) |entry| {
        try comp.settle(entry);
        program = try comp.drain();
    }
    var rest = comp.ownDecls(comp.moduleAt(index).decls);
    while (rest.next()) |decl_index| try comp.settle(decl_index);
    const others = try comp.drain();

    if (program.len == 0) program = others;
    std.sort.pdq(Pool.Instance, program, comp, beforeInSource);
    comp.ir.bodies = program;
    assert(comp.stack.items.len == 0);
}

fn settle(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!void {
    const origin = comp.declAt(decl_index).origin();
    try comp.ensure(.{ .decl = decl_index }, origin);

    const decl = comp.declAt(decl_index);
    if (decl.state == .poisoned or comp.isGeneric(decl_index)) return;
    switch (decl.kind) {
        .import, .type_alias, .unit_decl, .let => {},
        .extern_fn => {
            const instance = try comp.instantiate(decl_index, &.{}, origin);
            try comp.ensure(.{ .head = instance }, origin);
        },
        .fn_decl => try comp.enqueue(try comp.instantiate(decl_index, &.{}, origin)),
        .struct_decl => {
            if (decl.state != .done) return;
            const members = decl.answer.members;
            for (members.start..members.end()) |raw| try comp.settle(.from(raw));
        },
    }
}

fn enqueue(comp: *Compilation, instance: Pool.Instance) Allocator.Error!void {
    const kind = comp.declAt(comp.instanceDecl(instance)).kind;
    if (kind == .extern_fn) return;
    assert(kind == .fn_decl);
    if (comp.instanceAt(instance).queued) return;
    comp.instancePtr(instance).queued = true;
    try comp.queue.append(comp.gpa, instance);
}

fn drain(comp: *Compilation) Allocator.Error![]Pool.Instance {
    var drained: std.ArrayList(Pool.Instance) = .empty;
    var next: usize = 0;
    while (next < comp.queue.items.len) : (next += 1) {
        const instance = comp.queue.items[next];
        const origin = comp.instanceAt(instance).origin;
        try comp.ensure(.{ .head = instance }, origin);
        try comp.ensure(.{ .body = instance }, origin);
        try drained.append(comp.arena.allocator(), instance);

        const func = comp.funcOf(instance) orelse continue;
        const tags = comp.ir.insts.items(.tag);
        const data = comp.ir.insts.items(.data);
        const extra = comp.funcExtra(func);
        for (func.insts.start..func.insts.end()) |at| {
            if (tags[at] != .call) continue;
            try comp.enqueue(IR.callAt(extra, data[at].payload).callee);
        }
    }
    comp.queue.clearRetainingCapacity();
    return drained.items;
}

fn beforeInSource(comp: *const Compilation, a: Pool.Instance, b: Pool.Instance) bool {
    const one = comp.declAt(comp.instanceDecl(a));
    const other = comp.declAt(comp.instanceDecl(b));
    if (one.module != other.module) {
        return std.mem.lessThan(u8, comp.moduleAt(one.module).key, comp.moduleAt(other.module).key);
    }
    if (one.node != other.node) return one.node.int() < other.node.int();
    return a.int() < b.int();
}

pub fn ensure(comp: *Compilation, unit: Unit, origin: Origin) Allocator.Error!void {
    switch (comp.stateOf(unit).*) {
        .done, .poisoned => return,
        .in_progress => return comp.reportCycle(unit, origin),
        .unanalyzed => {},
    }

    if (comp.stack.items.len >= analyze_max) return comp.refuse(unit, origin, .{
        .code = .analysis_too_deep,
        .message = try comp.fmt(
            "checking this follows a chain more than {d} declarations deep",
            .{analyze_max},
        ),
        .label = "the chain stops here",
        .help = "a definition this far down a dependency chain is past what " ++
            "the compiler follows",
    });
    const deepest: Pool.OptionalInstance = switch (unit) {
        .decl => .none,
        .head, .body => |instance| instance.toOptional(),
    };
    if (deepest.unwrap()) |deep| if (comp.instanceAt(deep).depth > instantiate_max) {
        return comp.refuse(unit, origin, .{
            .code = .instantiates_too_deep,
            .message = try comp.fmt("this instantiates more than {d} levels deep", .{
                instantiate_max,
            }),
            .label = "the limit is here",
            .help = "a type or function that instantiates itself never bottoms out",
        });
    };

    comp.stateOf(unit).* = .in_progress;
    // the depth check above keeps this under what `init` reserved
    comp.stack.appendAssumeCapacity(.{ .unit = unit, .origin = origin });
    defer _ = comp.stack.pop();

    const marks = comp.scratch.mark();
    defer comp.scratch.restore(marks);

    const ok = switch (unit) {
        .decl => |decl_index| try comp.runDecl(decl_index),
        .head => |instance| switch (comp.declAt(comp.instanceDecl(instance)).kind) {
            .struct_decl => try Check.structRows(comp, instance),
            .type_alias => try Check.aliasInstance(comp, instance),
            .fn_decl, .extern_fn => try Check.fnSignature(comp, instance),
            .import, .unit_decl, .let => unreachable,
        },
        .body => |instance| switch (comp.declAt(comp.instanceDecl(instance)).kind) {
            .struct_decl => try Check.structEmbedding(comp, instance),
            .fn_decl => try Check.fnBody(comp, instance),
            .import, .type_alias, .unit_decl, .let, .extern_fn => unreachable,
        },
    };
    comp.stateOf(unit).* = if (ok) .done else .poisoned;
}

fn runDecl(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    const decl = comp.declAt(decl_index);
    if (decl.type_params > 0 and decl.kind != .extern_fn) return Check.declBounds(comp, decl_index);
    switch (decl.kind) {
        .import => return Module.resolveImport(comp, decl_index),
        .type_alias => return Check.typeAlias(comp, decl_index),
        .unit_decl => {
            _ = try comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
            return true;
        },
        .let => return Check.topLevelLet(comp, decl_index),
        .fn_decl => return true,
        .extern_fn => return Check.externDecl(comp, decl_index),
        .struct_decl => {
            const origin = decl.origin();
            const instance = try comp.instantiate(decl_index, &.{}, origin);
            try comp.ensure(.{ .head = instance }, origin);
            try comp.ensure(.{ .body = instance }, origin);
            return true;
        },
    }
}

/// Derived per call, because running a unit grows the tables.
fn stateOf(comp: *Compilation, unit: Unit) *Decl.State {
    return switch (unit) {
        .decl => |decl_index| &comp.declPtr(decl_index).state,
        .head => |instance| &comp.instancePtr(instance).head,
        .body => |instance| &comp.instancePtr(instance).body,
    };
}

fn refuse(
    comp: *Compilation,
    unit: Unit,
    origin: Origin,
    report_value: Diagnostic.Report,
) Allocator.Error!void {
    @branchHint(.cold);
    try comp.reportNode(origin.module, origin.node, report_value);
    comp.stateOf(unit).* = .poisoned;
}

fn reportCycle(comp: *Compilation, unit: Unit, origin: Origin) Allocator.Error!void {
    @branchHint(.cold);
    const name = try comp.unitName(unit);
    const kind = switch (unit) {
        .decl => |decl_index| comp.declAt(decl_index).kind,
        .head, .body => |instance| comp.declAt(comp.instanceDecl(instance)).kind,
    };
    const embedding = unit == .body and kind == .struct_decl;

    const circle = "this definition goes in a circle";
    const message = switch (kind) {
        .let => try comp.fmt("'{s}' takes its value from itself", .{name}),
        .type_alias => try comp.fmt("type '{s}' is an alias of itself", .{name}),
        .struct_decl => if (embedding)
            try comp.fmt("'{s}' holds itself by value, so it has no size", .{name})
        else
            circle,
        .import, .unit_decl, .fn_decl, .extern_fn => circle,
    };

    const position = for (comp.stack.items, 0..) |frame, at| {
        if (std.meta.eql(frame.unit, unit)) break at;
    } else unreachable; // in progress means on the stack

    const below = comp.stack.items[position + 1 ..];
    const chain = try comp.arena.allocator().alloc(Diagnostic.Note, below.len);
    for (below, chain) |frame, *note| {
        note.* = comp.noteAt(frame.origin.module, frame.origin.node, try comp.fmt(
            "which needs '{s}' here",
            .{try comp.unitName(frame.unit)},
        ));
    }

    try comp.reportNode(origin.module, origin.node, .{
        .code = if (embedding) .size_cycle else .value_cycle,
        .message = message,
        .label = "the circle closes here",
        .help = if (embedding)
            try comp.fmt("break the cycle with a pointer: '*{s}' or '*{s} | none'", .{ name, name })
        else
            null,
        .notes = chain,
    });
}

fn unitName(comp: *Compilation, unit: Unit) Allocator.Error![]const u8 {
    return switch (unit) {
        .decl => |decl_index| comp.pool.stringText(comp.declAt(decl_index).name),
        .head, .body => |instance| comp.instanceName(instance),
    };
}

pub fn instantiate(
    comp: *Compilation,
    decl_index: Decl.Index,
    args: []const Pool.Index,
    origin: Origin,
) Allocator.Error!Pool.Instance {
    switch (comp.declAt(decl_index).kind) {
        .struct_decl, .fn_decl, .extern_fn, .type_alias => {},
        .import, .unit_decl, .let => unreachable,
    }
    const gop = try comp.instance_map.getOrPut(comp.gpa, decl_index, args);
    if (gop.found_existing) return gop.value_ptr.*;

    if (comp.instances.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: Pool.Instance = .from(comp.instances.items.len);
    gop.value_ptr.* = index;

    const parent = comp.currentInstance();
    var depth: u32 = @intFromBool(args.len > 0);
    if (parent.unwrap()) |above| depth += comp.instanceAt(above).depth;

    try comp.instances.append(comp.gpa, .{
        .decl = decl_index,
        .args = gop.args,
        .type = .poison,
        .rows = .empty,
        .origin = origin,
        .parent = parent,
        .depth = depth,
        .func = .none,
        .head = .unanalyzed,
        .body = .unanalyzed,
        .queued = false,
    });
    // a type the moment it exists, so a struct can name itself
    if (comp.declAt(decl_index).kind == .struct_decl) {
        comp.instancePtr(index).type = try comp.pool.intern(comp.gpa, .{ .type_struct = index });
    }
    return index;
}

pub fn isGeneric(comp: *const Compilation, decl_index: Decl.Index) bool {
    const decl = comp.declAt(decl_index);
    if (decl.type_params > 0) return true;
    if (decl.owner.unwrap()) |owner| return comp.isGeneric(owner);
    return false;
}

/// The bounds of a declaration's own type parameters, copied out because
/// resolving them can grow the table. Null while they are still being
/// resolved, where a bound naming its own declaration reads as absent.
pub fn boundsOf(
    comp: *Compilation,
    decl_index: Decl.Index,
    origin: Origin,
    out: *[AST.type_params_max]Pool.Index,
) Allocator.Error!?[]const Pool.Index {
    const decl = comp.declAt(decl_index);
    if (decl.type_params == 0) return &.{};
    if (decl.state == .in_progress) return null;
    try comp.ensure(.{ .decl = decl_index }, origin);
    const found = comp.bounds.items[decl.bounds..][0..decl.type_params];
    @memcpy(out[0..found.len], found);
    return out[0..found.len];
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

pub fn instanceDecl(comp: *const Compilation, index: Pool.Instance) Decl.Index {
    return comp.instanceAt(index).decl;
}

pub fn instanceType(comp: *const Compilation, index: Pool.Instance) Pool.Index {
    return comp.instanceAt(index).type;
}

/// Invalidated by any other instantiation.
pub fn instanceArgs(comp: *const Compilation, index: Pool.Instance) []const Pool.Index {
    return comp.instanceAt(index).args.slice(comp.instance_map.lists.items);
}

/// Fields, or signature parameters. Invalidated by any other commit.
pub fn instanceRows(comp: *const Compilation, index: Pool.Instance) []const Row {
    return comp.instanceAt(index).rows.slice(comp.rows.items);
}

pub fn ensureRows(comp: *Compilation, index: Pool.Instance) Allocator.Error!void {
    try comp.ensure(.{ .head = index }, comp.declAt(comp.instanceDecl(index)).origin());
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
    assert(index.int() < comp.ir.funcs.items.len);
    return comp.ir.funcs.items[index.int()];
}

pub fn funcOf(comp: *const Compilation, instance: Pool.Instance) ?IR.Func {
    return comp.funcAt(comp.instanceAt(instance).func.unwrap() orelse return null);
}

pub fn funcBlocks(comp: *const Compilation, func: IR.Func) []const IR.Block {
    return func.blocks.slice(comp.ir.blocks.items);
}

pub fn funcExtra(comp: *const Compilation, func: IR.Func) []const u32 {
    return func.extra.slice(comp.ir.extra.items);
}

pub fn instAt(comp: *const Compilation, at: u32) IR.Inst {
    assert(at < comp.ir.insts.len);
    return comp.ir.insts.get(at);
}

pub fn commitFunc(comp: *Compilation, func: IR.Func) Allocator.Error!void {
    assert(comp.funcOf(func.instance) == null);
    try comp.ir.funcs.append(comp.gpa, func);
    const index: IR.Func.Index = .from(comp.ir.funcs.items.len - 1);
    comp.instancePtr(func.instance).func = index.toOptional();
}

pub fn ownDecls(comp: *const Compilation, range: Range) OwnDecls {
    return .{ .comp = comp, .range = range };
}

/// The declarations of a range that no struct owns.
pub const OwnDecls = struct {
    comp: *const Compilation,
    range: Range,
    at: u32 = 0,

    pub fn next(walk: *OwnDecls) ?Decl.Index {
        while (walk.at < walk.range.len) {
            const index: Decl.Index = .from(walk.range.at(walk.at));
            walk.at += 1;
            if (walk.comp.declAt(index).owner == .none) return index;
        }
        return null;
    }
};

pub fn rootDir(comp: *const Compilation) []const u8 {
    return std.fs.path.dirname(comp.options.root_path) orelse ".";
}

pub const entry_name = "main";

pub fn entryDecl(comp: *const Compilation) ?Decl.Index {
    return comp.moduleAt(.root).findDecl(entry_name);
}

pub fn hasErrors(comp: *const Compilation) bool {
    return comp.diagnostics.items.len > 0;
}

pub fn reportNode(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
    report_value: Diagnostic.Report,
) Allocator.Error!void {
    try comp.report(module, .{ .node = node }, report_value);
}

pub fn reportToken(
    comp: *Compilation,
    module: Module.Index,
    token: Token.Index,
    report_value: Diagnostic.Report,
) Allocator.Error!void {
    try comp.report(module, .{ .token = token }, report_value);
}

pub fn report(
    comp: *Compilation,
    module: Module.Index,
    anchor: Anchor,
    report_value: Diagnostic.Report,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(report_value.message.len > 0);

    const seen = try comp.reported.getOrPut(comp.gpa, .{
        .module = module,
        .code = report_value.code,
        .anchor = anchor,
    });
    if (seen.found_existing) return;
    if (comp.diagnostics.items.len >= diagnostics_max) return;

    const tree = comp.treeOf(module);
    const span: Diagnostic.Span = switch (anchor) {
        .node => |node| tree.nodeSpan(node),
        .token => |token| .{ .start = tree.tokenStart(token), .end = tree.tokenEnd(token) },
    };
    assert(span.start <= span.end);

    try comp.diagnostics.append(comp.gpa, .{
        .module = module,
        .unit = if (comp.stack.getLastOrNull()) |frame| frame.unit else null,
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

fn currentInstance(comp: *const Compilation) Pool.OptionalInstance {
    const frame = comp.stack.getLastOrNull() orelse return .none;
    return switch (frame.unit) {
        .decl => .none,
        .head, .body => |instance| instance.toOptional(),
    };
}

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

/// The notes, then the chain of instantiations the report was found inside.
fn withTrail(comp: *Compilation, notes_in: []const Diagnostic.Note) Allocator.Error![]Diagnostic.Note {
    const shown_max = 8;
    const head = shown_max / 2;

    var depth: u32 = 0;
    var current = comp.currentInstance();
    while (current.unwrap()) |instance| : (current = comp.instanceAt(instance).parent) {
        const row = comp.instanceAt(instance);
        depth += @intFromBool(row.args.len > 0);
        if (row.parent.unwrap()) |above| assert(above.int() < instance.int());
    }
    const elided = depth -| shown_max;
    const total = notes_in.len + depth - elided + @intFromBool(elided > 0);
    if (total == 0) return &.{};

    const out = try comp.arena.allocator().alloc(Diagnostic.Note, total);
    @memcpy(out[0..notes_in.len], notes_in);
    var at = notes_in.len;
    var position: u32 = 0;
    current = comp.currentInstance();
    while (current.unwrap()) |instance| : (current = comp.instanceAt(instance).parent) {
        const row = comp.instanceAt(instance);
        if (row.args.len == 0) continue;
        defer position += 1;
        if (position == head and elided > 0) {
            out[at] = .{ .message = try comp.fmt("and {d} more instantiation level{s}", .{
                elided, Check.plural(elided),
            }) };
            at += 1;
        }
        if (position >= head and position < head + elided) continue;
        out[at] = comp.noteAt(row.origin.module, row.origin.node, try comp.fmt(
            "while checking '{s}', needed here",
            .{try comp.instanceName(instance)},
        ));
        at += 1;
    }
    assert(at == total);
    return out;
}

pub fn noteAt(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
    message: []const u8,
) Diagnostic.Note {
    const owner = comp.moduleAt(module);
    return .{ .message = message, .span = owner.tree.nodeSpan(node), .source = &owner.source };
}

pub fn noteOne(
    comp: *Compilation,
    module: Module.Index,
    node: AST.Node.Index,
    message: []const u8,
) Allocator.Error![]Diagnostic.Note {
    return comp.arena.allocator().dupe(Diagnostic.Note, &.{comp.noteAt(module, node, message)});
}

pub fn fmt(
    comp: *Compilation,
    comptime template: []const u8,
    args: anytype,
) Allocator.Error![]const u8 {
    comptime assert(template.len > 0);
    return std.fmt.allocPrint(comp.arena.allocator(), template, args);
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
    for (comp.ir.bodies) |instance| {
        const func = comp.funcOf(instance) orelse continue;
        if (printed) try writer.writeByte('\n');
        printed = true;
        try Spell.writeFunc(comp, func, writer);
    }
}

fn spelled(comp: *Compilation, writer: anytype, subject: anytype) Allocator.Error![]const u8 {
    var out: Writer.Allocating = .init(comp.arena.allocator());
    writer(comp, &out.writer, subject) catch |err| switch (err) {
        error.WriteFailed => return error.OutOfMemory,
    };
    return out.written();
}

pub fn typeName(comp: *Compilation, index: Pool.Index) Allocator.Error![]const u8 {
    return comp.spelled(Spell.writeType, index);
}

pub fn instanceName(comp: *Compilation, index: Pool.Instance) Allocator.Error![]const u8 {
    return comp.spelled(Spell.writeInstance, index);
}

pub fn spellValue(comp: *Compilation, value: Pool.Index) Allocator.Error![]const u8 {
    return comp.spelled(Spell.writeConstantBare, value);
}

fn pathInside(outer: []const u8, inner: []const u8) bool {
    const trimmed = std.mem.trimEnd(u8, outer, "/");
    if (std.mem.startsWith(u8, inner, trimmed) == false) return false;
    if (inner.len == trimmed.len) return true;
    return inner[trimmed.len] == '/';
}

/// A map from an id and a list of arguments to a value, the lists kept here.
fn ArgsMap(comptime Id: type, comptime V: type) type {
    return struct {
        map: std.HashMapUnmanaged(Key, V, Context, load_percentage) = .empty,
        lists: std.ArrayList(Pool.Index) = .empty,

        const Self = @This();
        const load_percentage = std.hash_map.default_max_load_percentage;
        const Key = struct { id: Id, args: Range };
        const Lookup = struct { id: Id, args: []const Pool.Index };

        pub const empty: Self = .{};

        pub const GetOrPut = struct { found_existing: bool, value_ptr: *V, args: Range };

        pub fn deinit(self: *Self, gpa: Allocator) void {
            self.map.deinit(gpa);
            self.lists.deinit(gpa);
        }

        pub fn get(self: *const Self, id: Id, args: []const Pool.Index) ?V {
            const lookup: Lookup = .{ .id = id, .args = args };
            return self.map.getAdapted(lookup, Adapter{ .lists = self.lists.items });
        }

        pub fn getOrPut(
            self: *Self,
            gpa: Allocator,
            id: Id,
            args: []const Pool.Index,
        ) Allocator.Error!GetOrPut {
            // reserved first, so a key never points at arguments that failed to land
            try self.lists.ensureUnusedCapacity(gpa, args.len);
            const gop = try self.map.getOrPutContextAdapted(
                gpa,
                Lookup{ .id = id, .args = args },
                Adapter{ .lists = self.lists.items },
                Context{ .lists = self.lists.items },
            );
            if (gop.found_existing == false) {
                const start: u32 = @intCast(self.lists.items.len);
                self.lists.appendSliceAssumeCapacity(args);
                gop.key_ptr.* = .{ .id = id, .args = .since(start, self.lists.items.len) };
            }
            return .{
                .found_existing = gop.found_existing,
                .value_ptr = gop.value_ptr,
                .args = gop.key_ptr.args,
            };
        }

        fn hash(id: Id, args: []const Pool.Index) u64 {
            var hasher: std.hash.Wyhash = .init(@intFromEnum(id));
            hasher.update(std.mem.sliceAsBytes(args));
            return hasher.final();
        }

        const Context = struct {
            lists: []const Pool.Index,

            pub fn hash(context: Context, key: Key) u64 {
                return Self.hash(key.id, key.args.slice(context.lists));
            }

            pub fn eql(context: Context, a: Key, b: Key) bool {
                return a.id == b.id and std.mem.eql(
                    Pool.Index,
                    a.args.slice(context.lists),
                    b.args.slice(context.lists),
                );
            }
        };

        const Adapter = struct {
            lists: []const Pool.Index,

            pub fn hash(_: Adapter, lookup: Lookup) u64 {
                return Self.hash(lookup.id, lookup.args);
            }

            pub fn eql(adapter: Adapter, lookup: Lookup, key: Key) bool {
                return lookup.id == key.id and
                    std.mem.eql(Pool.Index, lookup.args, key.args.slice(adapter.lists));
            }
        };
    };
}

const testing = std.testing;

pub fn testCompile(comp: *Compilation, text: []const u8) !void {
    return testCompileFor(comp, text, .host);
}

pub fn testCompileFor(comp: *Compilation, text: []const u8, target: Target) !void {
    const gpa = testing.allocator;
    try comp.init(gpa, testing.io, .{
        .root_path = "test.phi",
        .std_dir = null,
        .target = target,
    });
    errdefer comp.deinit();

    const buffer = try gpa.alloc(u8, text.len + Source.padding);
    @memcpy(buffer[0..text.len], text);
    buffer[text.len] = 0;
    try comp.compile(.{ .path = "test.phi", .bytes = buffer[0..text.len :0] });
}

test "instantiation identity is index equality" {
    var comp: Compilation = undefined;
    try testCompile(&comp,
        \\pub type Box[T] = {
        \\    item: T
        \\}
        \\pub type Boxed = Box[i64]
        \\fn hold(a: Box[i64], b: Boxed, c: Box[u8]) Boxed {
        \\    return a
        \\}
        \\
    );
    defer comp.deinit();
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const hold = comp.moduleAt(.root).findDecl("hold") orelse return error.TestUnexpectedResult;
    const instance = try comp.instantiate(hold, &.{}, comp.declAt(hold).origin());
    const rows = comp.instanceRows(instance);
    try testing.expectEqual(3, rows.len);

    try testing.expectEqual(rows[0].type, rows[1].type);
    try testing.expectEqual(rows[1].type, comp.instanceType(instance));
    try testing.expect(rows[0].type != rows[2].type);
}

test "a generic alias is the type it names, not a new one" {
    var comp: Compilation = undefined;
    // `return b` compiles only because the alias and the union are one type
    try testCompile(&comp,
        \\type none
        \\type Maybe[T] = T | none
        \\fn pick(a: Maybe[i64], b: i64 | none) Maybe[i64] {
        \\    _ = a
        \\    return b
        \\}
        \\
    );
    defer comp.deinit();
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const pick = comp.moduleAt(.root).findDecl("pick") orelse return error.TestUnexpectedResult;
    const instance = try comp.instantiate(pick, &.{}, comp.declAt(pick).origin());
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
    try testCompile(&comp, deep.written());
    defer comp.deinit();
    try testing.expectEqual(0, comp.diagnostics.items.len);
    try testing.expectEqual(levels + 1, comp.ir.funcs.items.len);
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
    try testCompile(&comp, deep.written());
    defer comp.deinit();
    try testing.expectEqual(0, comp.diagnostics.items.len);
}

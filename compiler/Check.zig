const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Diagnostic = @import("Diagnostic.zig");
const Handle = @import("Handle.zig");
const IR = @import("IR.zig");
const Layout = @import("Layout.zig");
const Module = @import("Module.zig");
const Pool = @import("Pool.zig");
const Token = @import("Token.zig");
const Aggregate = @import("check/Aggregate.zig");
const Builtin = @import("check/Builtin.zig").Builtin;
const Call = @import("check/Call.zig");
const Expr = @import("check/Expr.zig");
const Flow = @import("check/Flow.zig");
const Narrowing = @import("check/Narrowing.zig");
const Place = @import("check/Place.zig");
const Resolve = @import("check/Resolve.zig");

const Closest = Diagnostic.Closest;
const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;

comp: *Compilation,
module_index: Module.Index,
module: *Module,
tree: *const AST,
bindings: []const Binding,
/// Null means constants only.
builder: ?*Builder,
/// Narrows below this belong to the unit that demanded this one.
narrows_floor: u32,
bool_type: Pool.Index,
none_type: Pool.Index,
/// Field types skip it, their struct gets its own walk.
demand_embedding: bool,

const Check = @This();

pub const type_params_max = AST.type_params_max;
pub const bindings_max = type_params_max * 2;
pub const call_args_max = 255;
pub const type_depth_max = AST.nest_max;

/// What `refOf` answers for a value that already reported, so it stays silent.
pub const broken_ref: Ref = .fromConstant(.poison);

pub const Binding = struct { name: Pool.String, type: Pool.Index, bound: ?Pool.Index };

pub const Operand = struct { value: Value, initializer: Node.OptionalIndex };

pub const Value = union(enum) {
    constant: Pool.Index,
    runtime: Runtime,
    diverged,
    poison,
    named_type: Pool.Index,
    named_generic: Decl.Index,
    named_fn: Decl.Index,
    named_module: Module.Index,

    const Runtime = struct { ref: Ref, type: Pool.Index };

    pub const void_value: Value = .{
        .runtime = .{ .ref = .fromConstant(.poison), .type = .void_type },
    };

    /// Poison has reported, and diverged has left.
    pub fn stops(value: Value) bool {
        return value == .poison or value == .diverged;
    }
};

/// What units stage and stack, shared so the capacity survives across them.
pub const Scratch = struct {
    rows: std.ArrayList(Compilation.Row) = .empty,
    narrows: std.ArrayList(Narrowing.Narrow) = .empty,
    facts: std.ArrayList(Narrowing.Fact) = .empty,
    operands: std.ArrayList(Operand) = .empty,
    builders: std.ArrayList(*Builder) = .empty,

    pub const Marks = struct { narrows: usize, facts: usize };

    /// Narrows and facts past the marks belong to the unit that took them.
    pub fn mark(scratch: *const Scratch) Marks {
        return .{ .narrows = scratch.narrows.items.len, .facts = scratch.facts.items.len };
    }

    pub fn restore(scratch: *Scratch, marks: Marks) void {
        scratch.narrows.shrinkRetainingCapacity(marks.narrows);
        scratch.facts.shrinkRetainingCapacity(marks.facts);
    }

    pub fn takeBuilder(scratch: *Scratch, gpa: Allocator) Allocator.Error!*Builder {
        try scratch.builders.ensureUnusedCapacity(gpa, 1);
        if (scratch.builders.pop()) |waiting| return waiting;
        const fresh = try gpa.create(Builder);
        fresh.* = .{};
        return fresh;
    }

    pub fn releaseBuilder(scratch: *Scratch, builder: *Builder) void {
        builder.clear();
        scratch.builders.appendAssumeCapacity(builder);
    }

    pub fn deinit(scratch: *Scratch, gpa: Allocator) void {
        for (scratch.builders.items) |builder| {
            builder.deinit(gpa);
            gpa.destroy(builder);
        }
        inline for (@typeInfo(Scratch).@"struct".fields) |field| {
            @field(scratch, field.name).deinit(gpa);
        }
        scratch.* = undefined;
    }
};

/// One body being lowered, reused across bodies for its capacity.
pub const Builder = struct {
    instance: Pool.Instance = undefined,
    return_type: Pool.Index = undefined,
    insts: IR.InstList = .empty,
    extra: std.ArrayList(u32) = .empty,
    blocks: std.ArrayList(Block) = .empty,
    current: IR.Block.Index = undefined,
    locals: std.ArrayList(Local) = .empty,
    names: std.AutoHashMapUnmanaged(Pool.String, Local.Index) = .empty,
    scopes: std.ArrayList(Scope) = .empty,
    defer_nodes: std.ArrayList(Node.Index) = .empty,
    loops: std.ArrayList(LoopFrame) = .empty,
    /// Scratch for `finishFunc`.
    block_map: std.ArrayList(u32) = .empty,
    frontier: std.ArrayList(u32) = .empty,
    /// Loops below this are outside the `defer` being emitted.
    defer_loops_floor: u32 = undefined,
    in_defer: bool = undefined,
    /// Unreachable code is still checked, then dropped.
    reachable: bool = undefined,

    /// The terminator is null while the block is still open.
    const Block = struct {
        first: u32,
        count: u32,
        terminator: ?IR.Terminator,

        fn ended(block: Block) IR.Terminator {
            return block.terminator orelse unreachable;
        }
    };

    pub const Local = struct {
        name: Pool.String,
        node: Node.Index,
        ref: Ref,
        /// A `var_slot` ref is a pointer to this.
        type: Pool.Index,
        shadowed: Index.Optional,
        kind: Kind,

        pub const Kind = enum(u8) { let, var_slot, param };
        pub const Index = Handle.Index("local");
    };

    const Scope = struct { locals_start: u32, defers_start: u32 };

    pub const LoopFrame = struct {
        /// `.empty` when the loop has no label.
        label: Pool.String,
        node: Node.Index,
        /// The `continue` target, which re-reads the condition.
        header: IR.Block.Index,
        exit: IR.Block.Index,
        scope_depth: u32,
        join: Flow.Join,
        broke_reachable: bool,
    };

    fn blockAt(builder: *Builder, index: IR.Block.Index) *Block {
        assert(index.int() < builder.blocks.items.len);
        return &builder.blocks.items[index.int()];
    }

    fn currentBlock(builder: *Builder) *Block {
        return builder.blockAt(builder.current);
    }

    fn clear(builder: *Builder) void {
        inline for (@typeInfo(Builder).@"struct".fields) |field| {
            if (@typeInfo(field.type) == .@"struct") {
                @field(builder, field.name).clearRetainingCapacity();
            }
        }
    }

    fn deinit(builder: *Builder, gpa: Allocator) void {
        inline for (@typeInfo(Builder).@"struct".fields) |field| {
            if (@typeInfo(field.type) == .@"struct") @field(builder, field.name).deinit(gpa);
        }
        builder.* = undefined;
    }
};

// The units. Each is one memoized answer, run through `Compilation.ensure`.

pub fn typeAlias(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const resolved = try check.aliasTarget(decl_index);
    comp.declPtr(decl_index).answer = .{ .type = resolved };
    return resolved != .poison;
}

pub fn aliasInstance(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, comp.instanceDecl(instance));
    try Resolve.bindTypeParams(&check, instance, &buffer);
    const resolved = try check.aliasTarget(comp.instanceDecl(instance));
    comp.instancePtr(instance).type = resolved;
    return resolved != .poison;
}

fn aliasTarget(check: *Check, decl_index: Decl.Index) Allocator.Error!Pool.Index {
    const view = check.tree.viewOf(check.declNode(decl_index)).alias_decl;
    return Resolve.resolveWrittenType(check, view.aliased);
}

pub fn topLevelLet(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const view = check.tree.viewOf(check.declNode(decl_index)).var_decl;

    // the annotation first, so a literal can land on what it says
    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try Resolve.resolveType(&check, type_expr)
    else
        null;

    var value = try check.checkValue(view.init_expr, annotation);
    assert(value != .runtime);
    assert(value != .diverged);
    if (annotation) |wanted| value = try check.coerce(value, wanted, view.init_expr);

    const met: Pool.Index = if (value == .constant) value.constant else .poison;
    comp.declPtr(decl_index).answer = .{ .constant = met };
    return met != .poison;
}

/// The bounds of a generic declaration's own type parameters, resolved once.
pub fn declBounds(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const decl = comp.declAt(decl_index);
    const params = Resolve.typeParamNodes(comp, decl_index)[1];
    assert(params.len == decl.type_params);
    for (params, 0..) |param, at| {
        const bound = try Resolve.boundOf(&check, decl_index, param);
        comp.bounds.items[decl.bounds + at] = bound orelse .poison;
    }
    return true;
}

pub fn structRows(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try Resolve.bindTypeParams(&check, instance, &buffer);
    check.demand_embedding = false;

    // staged, because resolving a field type can build other rows
    const mark = comp.scratch.rows.items.len;
    defer comp.scratch.rows.shrinkRetainingCapacity(mark);

    var clean = true;
    for (check.tree.viewOf(check.declNode(decl_index)).struct_decl.members) |member| {
        if (check.tree.nodeTag(member) != .field) continue;
        const field = check.tree.viewOf(member).field;
        const field_type = try Resolve.resolveType(&check, field.type_expr);
        if (field_type == .poison) clean = false;
        try check.stageRow(field.name_token, field_type, member);
    }
    try commitRows(comp, instance, mark);
    return clean;
}

pub fn structEmbedding(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl = comp.declAt(comp.instanceDecl(instance));
    try comp.ensure(.{ .head = instance }, decl.origin());

    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        // by index, because the walk can grow the rows table
        const row = comp.rowAt(.from(raw));
        try walkEmbedded(comp, row.type, .{ .module = decl.module, .node = row.node }, 0);
    }
    return true;
}

/// Every struct held by value inside a type, so a cycle among them reports.
pub fn walkEmbedded(
    comp: *Compilation,
    type_index: Pool.Index,
    from: Compilation.Origin,
    depth: u32,
) Allocator.Error!void {
    if (depth >= type_depth_max) return;
    switch (comp.pool.typeKey(type_index)) {
        .type_struct => |embedded| try comp.ensure(.{ .body = embedded }, from),
        .type_array => |array| try walkEmbedded(comp, array.child, from, depth + 1),
        .type_union => {
            var members = comp.pool.membersOf(type_index);
            while (members.next()) |member| try walkEmbedded(comp, member, from, depth + 1);
        },
        .type_simple, .type_unit, .type_pointer, .type_slice => {},
    }
}

pub fn externDecl(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const view = check.tree.viewOf(check.declNode(decl_index)).fn_decl;

    if (check.module.space != .std) {
        try check.failToken(view.name_token, .{
            .code = .builtin_outside_std,
            .message = "only the standard library declares an 'extern fn'",
            .label = "not available here",
            .help = "std wraps one in an ordinary function, so call that instead",
        });
        return false;
    }
    if (view.type_params.len > 0) {
        try check.failToken(view.name_token, .{
            .code = .extern_generic,
            .message = try comp.fmt("'{s}' is generic, and one symbol has one signature", .{
                comp.pool.stringText(comp.declAt(decl_index).name),
            }),
            .label = "cannot be generic",
            .help = "write one declaration per shape it is called with",
        });
        return false;
    }
    return true;
}

pub fn fnSignature(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try Resolve.bindTypeParams(&check, instance, &buffer);

    const view = check.tree.viewOf(check.declNode(decl_index)).fn_decl;

    // staged, because resolving a parameter type can build other rows
    const mark = comp.scratch.rows.items.len;
    defer comp.scratch.rows.shrinkRetainingCapacity(mark);

    var clean = true;
    for (view.params) |param_node| {
        if (check.tree.nodeTag(param_node) != .param) continue;
        const param = check.tree.viewOf(param_node).param;
        const name_text = check.tree.tokenSlice(param.name_token);

        const param_type = try Resolve.resolveWrittenType(&check, param.type_expr);
        if (param_type == .poison) clean = false;

        for (comp.scratch.rows.items[mark..]) |earlier| {
            if (comp.pool.sameText(earlier.name, name_text) == false) continue;
            try check.fail(param_node, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is already a parameter", .{name_text}),
                .label = "declared again here",
                .notes = try check.noteHere(earlier.node, "first declared here"),
            });
            clean = false;
            break;
        }
        if (view.is_extern) {
            if (try check.externCrosses(param_node, param_type, "parameter") == false) clean = false;
        }
        try check.stageRow(param.name_token, param_type, param_node);
    }
    try commitRows(comp, instance, mark);

    var return_type: Pool.Index = .void_type;
    if (view.return_type.unwrap()) |type_expr| {
        return_type = try Resolve.resolveWrittenType(&check, type_expr);
        if (view.is_extern) {
            if (try check.externCrosses(type_expr, return_type, "return type") == false) clean = false;
        }
    }
    comp.instancePtr(instance).type = return_type;
    return clean and return_type != .poison;
}

fn stageRow(
    check: *Check,
    name_token: Token.Index,
    type_index: Pool.Index,
    node: Node.Index,
) Allocator.Error!void {
    const comp = check.comp;
    try comp.scratch.rows.append(comp.gpa, .{
        .name = try comp.pool.string(comp.gpa, check.tree.tokenSlice(name_token)),
        .type = type_index,
        .node = node,
    });
}

fn commitRows(comp: *Compilation, instance: Pool.Instance, mark: usize) Allocator.Error!void {
    const staged = comp.scratch.rows.items[mark..];
    if (comp.rows.items.len + staged.len > std.math.maxInt(u32)) return error.OutOfMemory;

    const rows_start: u32 = @intCast(comp.rows.items.len);
    try comp.rows.appendSlice(comp.gpa, staged);
    comp.instancePtr(instance).rows = .since(rows_start, comp.rows.items.len);
}

fn externCrosses(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
) Allocator.Error!bool {
    const comp = check.comp;
    if (found == .poison) return true;

    const help: []const u8 = switch (comp.pool.keyOf(found)) {
        .type_simple => |simple| switch (simple) {
            .i8, .i16, .i32, .i64, .u8, .u16, .u32, .u64, .f32, .f64 => return true,
            .poison, .void, .untyped_int, .untyped_float, .untyped_aggregate => extern_help,
        },
        .type_pointer => return true,
        .type_union => union_help: {
            const it = Layout.niche(&comp.pool, found) orelse break :union_help extern_union_help;
            if (it.form == .pointer) return true;
            break :union_help extern_union_help;
        },
        .type_slice => "pass the address and the count, which '.ptr' and '.len' answer",
        .type_array => "pass a pointer to it, or slice it and pass '.ptr' and '.len'",
        .type_struct => "pass a pointer to it rather than the value",
        else => extern_help,
    };

    try check.fail(node, .{
        .code = .extern_signature,
        .message = try comp.fmt("a {s} crosses as a number or an address, and this is {s}", .{
            what,
            try comp.typeName(found),
        }),
        .label = try comp.fmt("this {s} cannot cross", .{what}),
        .help = help,
    });
    return false;
}

const extern_help = "the shapes that cross are 'i8' through 'i64', " ++
    "'u8' through 'u64', 'f32', 'f64', '*T', and '*T' beside a type with no values";

const extern_union_help = "a pointer beside a type with no values crosses, the " ++
    "null address standing for that member";

pub fn fnBody(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    if (comp.instanceAt(instance).head != .done) return false;

    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try Resolve.bindTypeParams(&check, instance, &buffer);

    const marks = comp.scratch.mark();
    const builder = try comp.scratch.takeBuilder(comp.gpa);
    defer comp.scratch.releaseBuilder(builder);

    builder.instance = instance;
    builder.return_type = comp.instanceType(instance);
    builder.current = .entry;
    builder.defer_loops_floor = 0;
    builder.in_defer = false;
    builder.reachable = true;
    check.builder = builder;
    try builder.insts.ensureTotalCapacity(comp.gpa, 64);

    const view = check.tree.viewOf(check.declNode(decl_index)).fn_decl;
    assert(view.is_extern == false);
    const body_node = view.body.unwrap() orelse return false;
    if (check.tree.nodeTag(body_node) != .block) return false;

    const entry = try check.newBlock();
    assert(entry == .entry);
    check.startBlock(entry);

    const rows = comp.instanceRows(instance);
    try builder.locals.ensureTotalCapacity(comp.gpa, rows.len + 8);
    for (rows) |row| {
        const param_ref = try check.emit(row.node, .param, row.type, .{ .name = row.name });
        try check.declareLocal(row.name, row.node, .param, param_ref, row.type);
    }

    _ = try check.checkBlockValue(body_node, .void_type);
    if (check.blockOpen()) {
        if (builder.reachable and builder.return_type != .void_type) {
            try check.failToken(view.name_token, .{
                .code = .missing_return,
                .message = try comp.fmt("not every path through '{s}' returns its {s}", .{
                    comp.pool.stringText(comp.declAt(decl_index).name),
                    try comp.typeName(builder.return_type),
                }),
                .label = "a path falls off the end",
                .help = "every path must end in 'return', or loop forever",
            });
        }
        check.endBlock(.{ .ret = .none });
    }
    assert(builder.scopes.items.len == 0);
    // every gather site restores its mark, nothing outlives the body
    assert(std.meta.eql(comp.scratch.mark(), marks));

    try check.finishFunc();
    return true;
}

fn context(comp: *Compilation, decl_index: Decl.Index) Check {
    const decl = comp.declAt(decl_index);
    const module = comp.moduleAt(decl.module);
    return .{
        .comp = comp,
        .module_index = decl.module,
        .module = module,
        .tree = &module.tree,
        .bindings = &.{},
        .builder = null,
        .narrows_floor = @intCast(comp.scratch.narrows.items.len),
        .bool_type = .poison,
        .none_type = .poison,
        .demand_embedding = true,
    };
}

fn declNode(check: *const Check, decl_index: Decl.Index) Node.Index {
    const decl = check.comp.declAt(decl_index);
    assert(decl.module == check.module_index);
    return decl.node;
}

pub fn mainTokenText(check: *const Check, node: Node.Index) []const u8 {
    return check.tree.tokenSlice(check.tree.nodeMainToken(node));
}

pub fn origin(check: *const Check, node: Node.Index) Compilation.Origin {
    return .{ .module = check.module_index, .node = node };
}

pub fn body(check: *const Check) *Builder {
    return check.builder orelse unreachable;
}

pub fn pointerTo(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = check.comp;
    return comp.pool.intern(comp.gpa, .{ .type_pointer = .{ .child = child, .mutable = mutable } });
}

pub fn sliceOf(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = check.comp;
    return comp.pool.intern(comp.gpa, .{ .type_slice = .{ .child = child, .mutable = mutable } });
}

// Lowering. Instructions, blocks, scopes, and locals of the body being built.

pub fn emit(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    data: IR.Inst.Data,
) Allocator.Error!Ref {
    const builder = check.body();
    assert(node.int() < check.tree.nodes.len);
    try check.reopenDead();

    if (builder.insts.len >= IR.Ref.inst_count_max) return error.OutOfMemory;
    const index: IR.Inst.Index = .from(builder.insts.len);
    try builder.insts.append(check.comp.gpa, .{
        .tag = tag,
        .type = type_index,
        .node = node,
        .data = data,
    });
    return .fromInst(index);
}

pub fn emitOne(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    operand: Ref,
) Allocator.Error!Ref {
    assert(operand != .none);
    return check.emit(node, tag, type_index, .{ .un = operand });
}

pub fn emitValue(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    data: IR.Inst.Data,
) Allocator.Error!Value {
    return runtimeValue(try check.emit(node, tag, type_index, data), type_index);
}

pub fn emitOneValue(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    operand: Ref,
) Allocator.Error!Value {
    return runtimeValue(try check.emitOne(node, tag, type_index, operand), type_index);
}

pub fn emitSlot(
    check: *Check,
    node: Node.Index,
    name: Pool.String,
    value_type: Pool.Index,
) Allocator.Error!Ref {
    const slot_type = try check.pointerTo(value_type, true);
    return check.emit(node, .local, slot_type, .{ .name = name });
}

pub fn emitStore(check: *Check, node: Node.Index, place: Ref, value: Ref) Allocator.Error!void {
    assert(place != .none);
    assert(value != .none);
    _ = try check.emit(node, .store, .void_type, .{ .bin = .{ .lhs = place, .rhs = value } });
}

pub fn emitExtra(
    check: *Check,
    header: []const u32,
    operands: []const Operand,
) Allocator.Error!IR.ExtraIndex {
    const builder = check.body();
    if (builder.extra.items.len + header.len + operands.len > std.math.maxInt(u32)) {
        return error.OutOfMemory;
    }

    const start: u32 = @intCast(builder.extra.items.len);
    try builder.extra.ensureUnusedCapacity(check.comp.gpa, header.len + operands.len);
    builder.extra.appendSliceAssumeCapacity(header);
    for (operands) |operand| {
        const ref = refOf(operand.value);
        assert(ref != .none);
        builder.extra.appendAssumeCapacity(@intFromEnum(ref));
    }
    return @enumFromInt(start);
}

pub fn newBlock(check: *Check) Allocator.Error!IR.Block.Index {
    const builder = check.body();
    if (builder.blocks.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: IR.Block.Index = .from(builder.blocks.items.len);
    try builder.blocks.append(check.comp.gpa, .{ .first = 0, .count = 0, .terminator = null });
    return index;
}

pub fn startBlock(check: *Check, block: IR.Block.Index) void {
    const builder = check.body();
    const opened = builder.blockAt(block);
    assert(opened.terminator == null);
    opened.first = @intCast(builder.insts.len);
    builder.current = block;
}

pub fn endBlock(check: *Check, terminator: IR.Terminator) void {
    const builder = check.body();
    const block = builder.currentBlock();
    assert(block.terminator == null);
    block.count = @as(u32, @intCast(builder.insts.len)) - block.first;
    block.terminator = terminator;
}

pub fn blockOpen(check: *const Check) bool {
    return check.body().currentBlock().terminator == null;
}

/// Closes the block with a jump, and says whether anything reachable flowed out.
pub fn jumpTo(check: *Check, target: IR.Block.Index) bool {
    if (check.blockOpen() == false) return false;
    const flowed = check.body().reachable;
    check.endBlock(.{ .jump = target });
    return flowed;
}

pub fn trap(check: *Check) Allocator.Error!void {
    try check.reopenDead();
    check.endBlock(.trap);
}

/// A closed block gets an unreachable successor, so what follows still checks.
pub fn reopenDead(check: *Check) Allocator.Error!void {
    const builder = check.body();
    if (builder.currentBlock().terminator == null) return;
    check.startBlock(try check.newBlock());
    builder.reachable = false;
    assert(check.blockOpen());
}

pub fn pushScope(check: *Check) Allocator.Error!void {
    const builder = check.body();
    try builder.scopes.append(check.comp.gpa, .{
        .locals_start = @intCast(builder.locals.items.len),
        .defers_start = @intCast(builder.defer_nodes.items.len),
    });
}

pub fn popScope(check: *Check) void {
    const builder = check.body();
    const scope = builder.scopes.pop() orelse unreachable;
    // innermost first, so a name bound twice inside the scope ends as it was outside it
    var index = builder.locals.items.len;
    while (index > scope.locals_start) {
        index -= 1;
        const local = builder.locals.items[index];
        if (local.shadowed.unwrap()) |outer| {
            builder.names.putAssumeCapacity(local.name, outer);
        } else {
            assert(builder.names.remove(local.name));
        }
    }
    builder.locals.shrinkRetainingCapacity(scope.locals_start);
    builder.defer_nodes.shrinkRetainingCapacity(scope.defers_start);
}

/// Emits the deferred statements of every scope above `target`, innermost first.
pub fn unwindScopesTo(check: *Check, target: u32) Allocator.Error!void {
    const builder = check.body();
    assert(target <= builder.scopes.items.len);

    var index = builder.scopes.items.len;
    var defers_end = builder.defer_nodes.items.len;
    while (index > target) {
        index -= 1;
        const scope = builder.scopes.items[index];
        var defer_index = defers_end;
        while (defer_index > scope.defers_start) {
            defer_index -= 1;
            try check.emitDefer(builder.defer_nodes.items[defer_index]);
        }
        defers_end = scope.defers_start;
    }
}

fn emitDefer(check: *Check, node: Node.Index) Allocator.Error!void {
    const builder = check.body();
    const outer = builder.in_defer;
    const floor = builder.defer_loops_floor;

    builder.in_defer = true;
    builder.defer_loops_floor = @intCast(builder.loops.items.len);
    defer {
        builder.in_defer = outer;
        builder.defer_loops_floor = floor;
    }
    try check.checkStatement(node);
}

pub fn declareLocal(
    check: *Check,
    name: Pool.String,
    node: Node.Index,
    kind: Builder.Local.Kind,
    ref: Ref,
    type_index: Pool.Index,
) Allocator.Error!void {
    const builder = check.body();
    const comp = check.comp;
    const text = comp.pool.stringText(name);

    const clash: ?Diagnostic.Report = clash: {
        if (builder.names.get(name)) |other| break :clash .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is already in scope", .{text}),
            .label = "shadows the outer one",
            .notes = try check.noteHere(check.localAt(other).node, "first bound here"),
        };
        for (check.bindings) |binding| {
            if (binding.name != name) continue;
            break :clash .{
                .code = .shadows,
                .message = try comp.fmt("'{s}' is a type parameter here", .{text}),
                .label = "shadows it",
            };
        }
        if (Pool.isPrimitiveName(name)) break :clash .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is the name of a type every file can see", .{text}),
            .label = "shadows it",
        };
        if (check.module.findDecl(text)) |decl_index| break :clash .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is already declared in this file", .{text}),
            .label = "shadows it",
            .notes = try check.noteHere(comp.declAt(decl_index).node, "declared here"),
        };
        break :clash null;
    };
    if (clash) |report| try check.fail(node, report);

    // room first, so a name never points at a local that failed to land
    try builder.locals.ensureUnusedCapacity(comp.gpa, 1);
    const index: Builder.Local.Index = .from(builder.locals.items.len);
    const gop = try builder.names.getOrPut(comp.gpa, name);
    builder.locals.appendAssumeCapacity(.{
        .name = name,
        .node = node,
        .ref = ref,
        .type = type_index,
        .shadowed = if (gop.found_existing) gop.value_ptr.toOptional() else .none,
        .kind = kind,
    });
    gop.value_ptr.* = index;
}

pub fn declarePoisoned(check: *Check, name: Pool.String, node: Node.Index) Allocator.Error!void {
    try check.declareLocal(name, node, .let, broken_ref, .poison);
}

/// Past a handful the table wins, which keeps a body of thousands linear.
const scan_max = 32;

pub fn findLocalIndex(check: *const Check, text: []const u8) ?Builder.Local.Index {
    const builder = check.builder orelse return null;
    const locals = builder.locals.items;

    if (locals.len > scan_max) {
        // declaring a local interns its name, so one nothing interned is no local
        const name = check.comp.pool.lookupString(text) orelse return null;
        return builder.names.get(name);
    }
    var index = locals.len;
    while (index > 0) {
        index -= 1;
        if (check.comp.pool.sameText(locals[index].name, text)) return .from(index);
    }
    return null;
}

pub fn localAt(check: *const Check, index: Builder.Local.Index) Builder.Local {
    const builder = check.body();
    assert(index.int() < builder.locals.items.len);
    return builder.locals.items[index.int()];
}

// Statements and blocks.

pub fn checkBlockValue(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(check.tree.nodeTag(node) == .block);
    const comp = check.comp;
    const statements = check.tree.viewOf(node).block;

    const builder = check.builder orelse return check.constantBlock(node, hint);

    try check.pushScope();
    const depth: u32 = @intCast(builder.scopes.items.len - 1);
    defer check.popScope();

    const narrows_mark = comp.scratch.narrows.items.len;
    defer comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);

    var value: Value = .void_value;
    for (statements, 0..) |statement, position| {
        if (check.blockOpen() == false or builder.reachable == false) {
            if (position > 0) try check.fail(statement, .{
                .code = .unreachable_code,
                .message = "this cannot be reached",
                .label = "never runs",
                .notes = try check.noteHere(statements[position - 1], "the block already left here"),
            });
            break;
        }
        const tail = position + 1 == statements.len;
        if (tail and wantsValue(hint) and tagIsStatement(check.tree.nodeTag(statement)) == false) {
            value = try check.checkExpr(statement, hint);
        } else {
            try check.checkStatement(statement);
        }
    }

    if (check.blockOpen() == false or builder.reachable == false) return .diverged;
    try check.unwindScopesTo(depth);
    return value;
}

fn constantBlock(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(check.builder == null);
    const statements = check.tree.viewOf(node).block;

    if (statements.len == 0) return .void_value;
    if (statements.len == 1 and tagIsStatement(check.tree.nodeTag(statements[0])) == false) {
        return check.checkExpr(statements[0], hint);
    }
    return check.needRuntime(node, "a block that holds statements");
}

fn tagIsStatement(tag: Node.Tag) bool {
    return switch (tag) {
        .var_decl, .assign, .defer_stmt, .err => true,
        else => false,
    };
}

fn checkStatement(check: *Check, node: Node.Index) Allocator.Error!void {
    assert(check.builder != null);
    switch (check.tree.viewOf(node)) {
        .var_decl => try check.checkVarDecl(node),
        .assign => |assign| try check.checkAssign(node, assign),
        .defer_stmt => |deferred| try check.body().defer_nodes.append(check.comp.gpa, deferred),
        .err => {},
        else => {
            const value = try check.checkExpr(node, .void_type);
            if (check.guardStatement(node)) |lhs| {
                const mark: u32 = @intCast(check.comp.scratch.facts.items.len);
                defer check.comp.scratch.facts.shrinkRetainingCapacity(mark);
                try Narrowing.applyFacts(check, (try Narrowing.gatherFacts(check, lhs)).when_true);
                return;
            }
            try check.expectNothing(node, value);
        },
    }
}

/// `x is T or return`, whose left side holds for the rest of the block.
fn guardStatement(check: *const Check, node: Node.Index) ?Node.Index {
    if (check.tree.nodeTag(node) != .binary) return null;
    const view = check.tree.viewOf(node).binary;
    if (view.op != .bool_or) return null;
    return switch (check.tree.nodeTag(view.rhs)) {
        .return_expr, .break_expr, .continue_expr => view.lhs,
        else => null,
    };
}

fn checkVarDecl(check: *Check, node: Node.Index) Allocator.Error!void {
    const comp = check.comp;
    const view = check.tree.viewOf(node).var_decl;
    const name_text = check.tree.tokenSlice(view.name_token);

    if (Module.isDiscard(name_text)) return check.failDiscard(node);
    const name = try comp.pool.string(comp.gpa, name_text);

    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try Resolve.resolveWrittenType(check, type_expr)
    else
        null;

    var value = try check.checkValue(view.init_expr, annotation);
    if (annotation) |wanted| value = try check.coerce(value, wanted, view.init_expr);

    const value_type = check.typeOf(value);
    if (value_type == .void_type) {
        try check.fail(view.init_expr, .{
            .code = .type_mismatch,
            .message = "this produces nothing, so there is nothing to bind",
            .label = "no value here",
        });
        return check.declarePoisoned(name, node);
    }
    if (value_type == .poison) return check.declarePoisoned(name, node);

    if (view.is_mutable and value == .constant and Pool.isUntyped(value_type)) {
        assert(annotation == null);
        const example: ?[]const u8 = switch (comp.pool.keyOf(value.constant)) {
            .value_int => "i64",
            .value_float => "f64",
            .value_aggregate => |it| try comp.fmt("[{d}]{s}", .{
                it.elems.len,
                try Aggregate.elementExample(check, it),
            }),
            else => null,
        };
        if (example) |shape| {
            try check.fail(node, .{
                .code = .var_needs_type,
                .message = try comp.fmt("'{s}' needs a type before it can vary", .{name_text}),
                .label = "no type to hold it",
                .help = try comp.fmt("write 'var {s}: {s} = ...', or whichever type is meant", .{
                    name_text, shape,
                }),
            });
            return check.declarePoisoned(name, node);
        }
    }

    if (view.is_mutable) {
        const slot = try check.emitSlot(node, name, value_type);
        try check.emitStore(node, slot, refOf(value));
        return check.declareLocal(name, node, .var_slot, slot, value_type);
    }
    try check.declareLocal(name, node, .let, refOf(value), value_type);
}

fn checkAssign(check: *Check, node: Node.Index, assign: AST.View.Assign) Allocator.Error!void {
    if (assign.op == null and check.tree.nodeTag(assign.lhs) == .ident) {
        if (Module.isDiscard(check.mainTokenText(assign.lhs))) {
            _ = try check.checkValue(assign.rhs, null);
            return;
        }
    }

    const place = try Place.checkPlace(check, assign.lhs) orelse {
        _ = try check.checkExpr(assign.rhs, null);
        return;
    };
    if (place.immutable) |why| {
        try Place.reportImmutable(check, assign.lhs, place, why);
        _ = try check.checkExpr(assign.rhs, place.type);
        return;
    }
    assert(place.kind == .address);
    if (place.type == .poison) return;

    const value: Value = if (assign.op) |op| folded: {
        const held = try Place.placeValue(check, place);
        const rhs = try check.checkValue(assign.rhs, place.type);
        if (rhs.stops()) return;
        break :folded try Expr.combine(check, .{
            .node = node,
            .op = op,
            .op_token = assign.op_token,
            .lhs = runtimeValue(held, place.type),
            .lhs_node = assign.lhs,
            .rhs = rhs,
            .rhs_node = assign.rhs,
        });
    } else try check.checkExpr(assign.rhs, place.type);

    const met = try check.coerce(value, place.type, assign.rhs);
    if (met == .poison) return;
    try check.emitStore(node, place.ref, refOf(met));
}

// Expressions. The dispatcher, and what every kind of value answers.

pub fn checkExpr(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    if (check.builder == null) {
        if (runtimeOnly(check.tree.nodeTag(node))) |what| return check.needRuntime(node, what);
    }

    switch (check.tree.viewOf(node)) {
        .builtin => return Builtin.notAValue(check, node),
        .ident => return Expr.checkIdent(check, node),
        .number_literal => return Expr.checkNumber(check, node),
        .string_literal => return Expr.checkString(check, node),
        .multiline_string => |view| return Expr.checkMultilineString(check, view),
        .char_literal => return Expr.checkChar(check, node),
        .block => return check.checkBlockValue(node, hint),
        .if_expr => |view| return Flow.checkIf(check, node, view, hint),
        .loop_expr => |view| return Flow.checkLoop(check, node, view, hint),
        .match_expr => |view| return Flow.checkMatch(check, node, view, hint),
        .return_expr => |operand| return Flow.checkReturn(check, node, operand),
        .break_expr => |view| return Flow.checkBreak(check, node, view),
        .continue_expr => |label| return Flow.checkContinue(check, node, label),
        .binary => |view| return Expr.checkBinary(check, node, view, hint),
        .unary => |view| return Expr.checkUnary(check, node, view),
        .is_expr => |view| return Narrowing.checkIs(check, node, view),
        .or_bind => |view| return Flow.checkOrBind(check, node, view, hint),
        .field_access => |view| return Expr.checkFieldAccess(check, node, view),
        .deref => return Place.checkDeref(check, node),
        .call => return Call.checkCall(check, node, hint),
        .bracket => |view| return Aggregate.checkBracketExpr(check, node, view),
        .struct_literal => return Aggregate.checkStructLiteral(check, node, hint),
        .array_literal => return Aggregate.checkArrayLiteral(check, node, hint),
        .array_type, .slice_type, .pointer_type, .union_type => {
            const resolved = try Resolve.resolveType(check, node);
            return if (resolved == .poison) .poison else .{ .named_type = resolved };
        },
        .err => return .poison,
        .root, .import_decl, .struct_decl, .alias_decl, .unit_decl, .fn_decl => unreachable,
        .var_decl, .type_param, .param, .field, .assign, .defer_stmt => unreachable,
        .match_arm, .struct_field_init, .range_expr => unreachable,
    }
}

/// A branch is not here, because a settled one picks its arm.
fn runtimeOnly(tag: Node.Tag) ?[]const u8 {
    return switch (tag) {
        .loop_expr => "a loop",
        .return_expr => "'return'",
        .break_expr => "'break'",
        .continue_expr => "'continue'",
        .deref => "reading through a pointer",
        .or_bind => "an 'or' handler",
        else => null,
    };
}

pub fn checkValue(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const value = try check.checkExpr(node, hint);
    return if (try check.valueOnly(node, value)) value else .poison;
}

pub fn valueOnly(check: *Check, node: Node.Index, value: Value) Allocator.Error!bool {
    const report: Diagnostic.Report = switch (value) {
        .constant, .runtime, .poison, .diverged => return true,
        .named_type, .named_generic => .{
            .code = .type_as_value,
            .message = "types are not values",
            .label = "a type, where a value belongs",
            .help = "a type stands where a type is written, before '.', and after 'is' or 'match'",
        },
        .named_fn => .{
            .code = .not_a_function,
            .message = "a function is not a value, so call it",
            .label = "missing the call",
            .help = "there are no function values in the language",
        },
        .named_module => .{
            .code = .type_as_value,
            .message = "a module is not a value",
            .label = "a module, where a value belongs",
        },
    };
    try check.fail(node, report);
    return false;
}

pub fn expectNothing(check: *Check, node: Node.Index, value: Value) Allocator.Error!void {
    if (try check.valueOnly(node, value) == false) return;
    const found = check.typeOf(value);
    if (found == .void_type or found == .poison) return;

    try check.fail(node, .{
        .code = .value_unused,
        .message = if (check.typeCanHold(found))
            try check.comp.fmt("this {s} goes nowhere", .{try check.comp.typeName(found)})
        else
            "this value goes nowhere",
        .label = "unused value",
        .help = "bind it, return it, or drop it with '_ ='",
    });
}

pub fn needRuntime(check: *Check, node: Node.Index, what: []const u8) Allocator.Error!Value {
    assert(check.builder == null);
    return check.refuse(node, .{
        .code = .not_constant,
        .message = try check.comp.fmt(
            "this must settle before anything runs, and {s} happens at run time",
            .{what},
        ),
        .label = "not a constant",
        .help = "the constant set is literals, names of constants, operators, and parentheses",
    });
}

pub fn typeOf(check: *const Check, value: Value) Pool.Index {
    return switch (value) {
        .constant => |constant| check.comp.pool.typeOfValue(constant),
        .runtime => |runtime| runtime.type,
        .poison, .diverged => .poison,
        .named_type, .named_generic, .named_fn, .named_module => .poison,
    };
}

pub fn refOf(value: Value) Ref {
    return switch (value) {
        .constant => |constant| .fromConstant(constant),
        .runtime => |runtime| runtime.ref,
        .diverged, .poison => broken_ref,
        .named_type, .named_generic, .named_fn, .named_module => broken_ref,
    };
}

pub fn runtimeValue(ref: Ref, type_index: Pool.Index) Value {
    return .{ .runtime = .{ .ref = ref, .type = type_index } };
}

pub fn untypedInt(check: *Check, value: i128) Allocator.Error!Value {
    return .{ .constant = try check.comp.pool.int(check.comp.gpa, .untyped_int_type, value) };
}

pub fn typeCanHold(check: *const Check, type_index: Pool.Index) bool {
    if (type_index == .void_type) return false;
    if (Pool.isUntyped(type_index)) return false;
    return check.comp.pool.isType(type_index);
}

pub fn wantsValue(hint: ?Pool.Index) bool {
    const wanted = hint orelse return true;
    return wanted != .void_type;
}

/// Two unit members, the first meaning yes. `bool` is declared, never built in.
pub fn boolType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    if (check.bool_type == .poison) check.bool_type = try check.preludeType(node, .bool);
    return check.bool_type;
}

pub fn noneType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    if (check.none_type == .poison) check.none_type = try check.preludeType(node, .none);
    return check.none_type;
}

fn preludeType(
    check: *Check,
    node: Node.Index,
    which: enum { bool, none },
) Allocator.Error!Pool.Index {
    const pool = &check.comp.pool;
    const name = switch (which) {
        .bool => Module.bool_name,
        .none => Module.none_name,
    };
    if (Resolve.visibleDecl(check, name)) |decl_index| {
        const found = try Resolve.declAsType(check, decl_index, node);
        const shaped = switch (which) {
            .bool => pool.isUnion(found) and pool.unionMemberCount(found) == 2 and
                pool.keyOf(pool.unionMemberAt(found, 0)) == .type_unit and
                pool.keyOf(pool.unionMemberAt(found, 1)) == .type_unit,
            .none => pool.keyOf(found) == .type_unit,
        };
        if (shaped) return found;
    }
    try check.fail(node, switch (which) {
        .bool => .{
            .code = .no_prelude_type,
            .message = "this needs 'bool', a union of two unit types",
            .label = "no such 'bool' in scope",
            .help = "declare 'type true', 'type false', and 'type bool = true | false'",
        },
        .none => .{
            .code = .no_prelude_type,
            .message = "this needs 'none', a unit type",
            .label = "no such 'none' in scope",
            .help = "declare 'type none'",
        },
    });
    return .poison;
}

pub fn settledTruth(check: *Check, node: Node.Index, holds: bool) Allocator.Error!Value {
    const bools = try check.boolType(node);
    return .{ .constant = try check.comp.pool.truth(check.comp.gpa, bools, holds) };
}

pub fn truthOf(check: *const Check, bools: Pool.Index, constant: Pool.Index) ?bool {
    if (bools == .poison) return null;
    const pool = &check.comp.pool;
    const found = pool.memberOfValue(constant);
    if (found == pool.unionMemberAt(bools, 0)) return true;
    if (found == pool.unionMemberAt(bools, 1)) return false;
    return null;
}

// Coercion, the one place a value meets the type it lands on.

pub fn coerce(
    check: *Check,
    value: Value,
    wanted: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    if (wanted == .poison) return .poison;

    switch (value) {
        .poison => return .poison,
        .diverged => return .diverged,
        .constant => |constant| return check.fitValue(constant, wanted, node),
        .runtime => |runtime| {
            if (runtime.type == wanted) return value;
            if (runtime.type == .poison) return .poison;

            if (Pool.widens(runtime.type, wanted)) {
                return check.emitOneValue(node, .widen, wanted, runtime.ref);
            }
            if (writesThrough(&comp.pool, runtime.type, wanted)) |writable| {
                if (writable) return runtimeValue(runtime.ref, wanted);
                try check.failNeedsWritable(node, runtime.type, wanted);
                return .poison;
            }
            if (comp.pool.isUnion(wanted)) {
                if (comp.pool.subsumes(wanted, runtime.type)) {
                    return check.emitValue(node, .union_init, wanted, .{
                        .probe = .{ .operand = runtime.ref, .member = runtime.type },
                    });
                }
                if (unionMemberFor(&comp.pool, wanted, runtime.type)) |member| {
                    // membership settles the second step, so it cannot come back here
                    const met = try check.coerce(value, member, node);
                    if (met == .poison) return .poison;
                    return check.coerce(met, wanted, node);
                }
            }
            return check.reportMismatch(node, value, wanted);
        },
        else => {
            _ = try check.valueOnly(node, value);
            return .poison;
        },
    }
}

fn writesThrough(pool: *const Pool, have: Pool.Index, want: Pool.Index) ?bool {
    const from = pool.keyOf(have);
    const to = pool.keyOf(want);
    if (std.meta.activeTag(from) != std.meta.activeTag(to)) return null;

    return switch (from) {
        .type_pointer => |it| if (it.child == to.type_pointer.child) it.mutable else null,
        .type_slice => |it| if (it.child == to.type_slice.child) it.mutable else null,
        else => null,
    };
}

fn unionMemberFor(pool: *const Pool, wanted: Pool.Index, found: Pool.Index) ?Pool.Index {
    assert(pool.isUnion(wanted));
    assert(pool.unionHas(wanted, found) == false);
    for (pool.unionMembers(wanted)) |member| {
        if (Pool.widens(found, member)) return member;
        // permission is only ever given up, never gained
        if (writesThrough(pool, found, member)) |writable| if (writable) return member;
    }
    return null;
}

fn failNeedsWritable(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    wanted: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;
    try check.fail(node, .{
        .code = .write_through_pointer,
        .message = try comp.fmt("this is {s}, and {s} is needed to write", .{
            try comp.typeName(found),
            try comp.typeName(wanted),
        }),
        .label = "read-only",
        .help = switch (comp.pool.keyOf(wanted)) {
            .type_slice => "take '[]var' where the view is made",
            else => "take '*var' where the pointer is made",
        },
    });
}

pub fn fitValue(
    check: *Check,
    constant: Pool.Index,
    wanted: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    if (constant == .poison or wanted == .poison) return .poison;
    return switch (try comp.pool.fit(comp.gpa, constant, wanted, .allowed)) {
        .value => |final| .{ .constant = final },
        .does_not_fit => fitted: {
            try check.fail(node, try check.doesNotFit(constant, wanted, "an untyped constant " ++
                "takes any type its value fits, and this value does not fit this one"));
            break :fitted .poison;
        },
        .wrong_kind => try check.reportMismatch(node, .{ .constant = constant }, wanted),
    };
}

pub fn doesNotFit(
    check: *Check,
    constant: Pool.Index,
    wanted: Pool.Index,
    help: ?[]const u8,
) Allocator.Error!Diagnostic.Report {
    return .{
        .code = .does_not_fit,
        .message = try check.comp.fmt("{s} does not fit in {s}", .{
            try check.comp.spellValue(constant),
            try check.comp.typeName(wanted),
        }),
        .label = "past the type's edge",
        .help = help,
    };
}

fn reportMismatch(
    check: *Check,
    node: Node.Index,
    value: Value,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const found = check.typeOf(value);

    const narrowable = found != .poison and wanted != .poison and
        comp.pool.isUnion(found) and comp.pool.subsumes(found, wanted);
    const help: []const u8 = help: {
        if (narrowable) break :help Expr.narrow_help;
        if (Pool.isSizedInt(found) and Pool.isSizedInt(wanted)) {
            break :help "'@int_cast(...)' converts, and '@int_fits(...)' answers 'none' " ++
                "where a value does not fit";
        }
        if (comp.pool.keyOf(wanted) == .type_slice) {
            const view = comp.pool.keyOf(wanted).type_slice;
            if (comp.pool.keyOf(found) == .type_array) {
                if (comp.pool.keyOf(found).type_array.child == view.child) {
                    break :help "slice it to make a view of it, as in 'a[0..]'";
                }
            }
            if (found == .untyped_aggregate_type and view.mutable) {
                break :help "a constant makes '[]T' and never '[]var T', because the " ++
                    "program's own bytes are read-only";
            }
        }
        break :help "nothing converts on its own";
    };

    return check.refuse(node, .{
        .code = if (narrowable) .not_narrowed else .type_mismatch,
        .message = try comp.fmt("expected {s}, found {s}", .{
            try comp.typeName(wanted),
            try comp.typeName(found),
        }),
        .label = "the wrong type",
        .help = help,
    });
}

// Reporting.

pub fn fail(check: *Check, node: Node.Index, report: Diagnostic.Report) Allocator.Error!void {
    try check.comp.reportNode(check.module_index, node, report);
}

pub fn failToken(
    check: *Check,
    token: Token.Index,
    report: Diagnostic.Report,
) Allocator.Error!void {
    try check.comp.reportToken(check.module_index, token, report);
}

pub fn refuse(check: *Check, node: Node.Index, report: Diagnostic.Report) Allocator.Error!Value {
    try check.fail(node, report);
    return .poison;
}

pub fn refuseToken(
    check: *Check,
    token: Token.Index,
    report: Diagnostic.Report,
) Allocator.Error!Value {
    try check.failToken(token, report);
    return .poison;
}

pub fn noteHere(
    check: *Check,
    node: Node.Index,
    message: []const u8,
) Allocator.Error![]Diagnostic.Note {
    return check.comp.noteOne(check.module_index, node, message);
}

pub fn failDiscard(check: *Check, node: Node.Index) Allocator.Error!void {
    try check.fail(node, .{
        .code = .discard_reserved,
        .message = "'_' is not a name, and only discards a value",
        .label = "not a name",
        .help = "write '_ = expression' to drop a value on purpose",
    });
}

pub fn reportUndefined(check: *Check, node: Node.Index, text: []const u8) Allocator.Error!void {
    try check.fail(node, .{
        .code = .undefined_name,
        .message = try check.comp.fmt("nothing named '{s}' is in scope here", .{text}),
        .label = "unknown name",
        .help = try check.suggestName(text),
    });
}

fn suggestName(check: *Check, text: []const u8) Allocator.Error!?[]const u8 {
    const comp = check.comp;
    var closest: Closest = .{ .target = text };

    if (check.builder) |builder| {
        for (builder.locals.items) |local| closest.consider(comp.pool.stringText(local.name));
    }
    for (check.bindings) |binding| closest.consider(comp.pool.stringText(binding.name));
    considerDecls(comp, &closest, check.module.decls);
    if (comp.prelude) |prelude| {
        if (prelude != check.module_index) considerDecls(comp, &closest, comp.moduleAt(prelude).decls);
    }
    for (Pool.primitive_names) |name| closest.consider(name);

    return closest.didYouMean(comp.arena.allocator());
}

fn considerDecls(comp: *const Compilation, closest: *Closest, range: Compilation.Range) void {
    var walk = comp.ownDecls(range);
    while (walk.next()) |index| closest.consider(comp.pool.stringText(comp.declAt(index).name));
}

pub const Arguments = enum { value, type };

pub fn failArity(
    check: *Check,
    node: Node.Index,
    name: []const u8,
    of: Arguments,
    wanted: u64,
    written: usize,
    notes: []const Diagnostic.Note,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = switch (of) {
            .value => .wrong_arity,
            .type => .generic_arguments,
        },
        .message = switch (of) {
            .value => try check.comp.fmt("'{s}' takes {d} argument{s}, and this call has {d}", .{
                name, wanted, plural(wanted), written,
            }),
            .type => try check.comp.fmt("'{s}' takes {d} type argument{s}, and this writes {d}", .{
                name, wanted, plural(wanted), written,
            }),
        },
        .label = "wrong number of arguments",
        .notes = notes,
    });
}

pub fn plural(count: u64) []const u8 {
    return if (count == 1) "" else "s";
}

pub fn quotedList(
    comp: *Compilation,
    so_far: []const u8,
    name: []const u8,
) Allocator.Error![]const u8 {
    if (so_far.len == 0) return comp.fmt("'{s}'", .{name});
    return comp.fmt("{s}, '{s}'", .{ so_far, name });
}

// The commit. Reachable blocks renumbered, then everything appended to the program.

const block_dead = std.math.maxInt(u32);

fn finishFunc(check: *Check) Allocator.Error!void {
    const comp = check.comp;
    const gpa = comp.gpa;
    const builder = check.body();
    const block_count = builder.blocks.items.len;
    assert(block_count > 0);
    assert(builder.block_map.items.len == 0);
    assert(builder.frontier.items.len == 0);

    try builder.block_map.appendNTimes(gpa, block_dead, block_count);
    try builder.frontier.ensureTotalCapacity(gpa, block_count);

    const map = builder.block_map.items;
    map[0] = 0;
    builder.frontier.appendAssumeCapacity(0);
    while (builder.frontier.pop()) |raw| {
        switch (builder.blocks.items[raw].ended()) {
            .jump => |target| finishFuncVisit(map, &builder.frontier, target.int()),
            .branch => |branch| {
                finishFuncVisit(map, &builder.frontier, branch.then_block.int());
                finishFuncVisit(map, &builder.frontier, branch.else_block.int());
            },
            .ret, .trap => {},
        }
    }

    // only blocks are renumbered, so every instruction ref stays valid
    var live_blocks: u32 = 0;
    for (map) |*slot| {
        if (slot.* != block_dead) {
            slot.* = live_blocks;
            live_blocks += 1;
        }
    }
    assert(live_blocks > 0);

    const blocks_start: u32 = @intCast(comp.ir.blocks.items.len);
    try comp.ir.blocks.ensureUnusedCapacity(gpa, live_blocks);
    for (builder.blocks.items, map) |block, slot| {
        if (slot == block_dead) continue;
        comp.ir.blocks.appendAssumeCapacity(.{
            .first = block.first,
            .count = block.count,
            .terminator = switch (block.ended()) {
                .jump => |target| .{ .jump = @enumFromInt(map[target.int()]) },
                .branch => |branch| .{ .branch = .{
                    .cond = branch.cond,
                    .then_block = @enumFromInt(map[branch.then_block.int()]),
                    .else_block = @enumFromInt(map[branch.else_block.int()]),
                } },
                .ret => |value| .{ .ret = value },
                .trap => .trap,
            },
        });
    }

    const inst_count: u32 = @intCast(builder.insts.len);
    if (comp.ir.insts.len + inst_count > std.math.maxInt(u32)) return error.OutOfMemory;
    const insts_start: u32 = @intCast(comp.ir.insts.len);
    try comp.ir.insts.resize(gpa, comp.ir.insts.len + inst_count);
    const from = builder.insts.slice();
    const into = comp.ir.insts.slice();
    inline for (std.enums.values(IR.InstList.Field)) |column| {
        @memcpy(into.items(column)[insts_start..], from.items(column));
    }

    // the pair of the range assertion `emit` makes on the way in
    const tree_nodes = check.tree.nodes.len;
    for (into.items(.node)[insts_start..]) |node| assert(node.int() < tree_nodes);

    const extra_start: u32 = @intCast(comp.ir.extra.items.len);
    try comp.ir.extra.appendSlice(gpa, builder.extra.items);

    try comp.commitFunc(.{
        .instance = builder.instance,
        .insts = .since(insts_start, comp.ir.insts.len),
        .extra = .since(extra_start, comp.ir.extra.items.len),
        .blocks = .since(blocks_start, comp.ir.blocks.items.len),
    });
}

fn finishFuncVisit(map: []u32, frontier: *std.ArrayList(u32), target: u32) void {
    if (map[target] != block_dead) return;
    map[target] = 0;
    frontier.appendAssumeCapacity(target);
}

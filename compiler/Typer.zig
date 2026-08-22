//! Types a declaration and lowers its body to IR.

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
const Source = @import("Source.zig");
const Token = @import("Token.zig");
const Aggregate = @import("typer/Aggregate.zig");
const Builtin = @import("typer/Builtin.zig").Builtin;
const Call = @import("typer/Call.zig");
const Expr = @import("typer/Expr.zig");
const Flow = @import("typer/Flow.zig");
const Narrow = @import("typer/Narrow.zig");
const Place = @import("typer/Place.zig");
const Resolve = @import("typer/Resolve.zig");

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

const Typer = @This();

pub const type_params_max = AST.type_params_max;
pub const bindings_max = type_params_max * 2;
pub const call_args_max = 255;
pub const type_depth_max = AST.nest_max;

/// What `refOf` answers for a value that already reported, so it stays silent.
pub const broken_ref: Ref = .fromConstant(.poison);

pub const Binding = struct {
    name: Pool.String,
    type: Pool.Index,
    bound: ?Pool.Index,
    node: Node.Index,
};

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

pub const Scratch = struct {
    rows: std.ArrayList(Compilation.Row) = .empty,
    narrows: std.ArrayList(Narrow.Narrow) = .empty,
    facts: std.ArrayList(Narrow.Fact) = .empty,
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

pub fn typeAlias(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var typer = context(comp, decl_index);
    const resolved = try typer.aliasTarget(decl_index);
    comp.declPtr(decl_index).answer = .{ .type = resolved };
    return resolved != .poison;
}

pub fn aliasInstance(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    var buffer: [bindings_max]Binding = undefined;
    var typer = context(comp, comp.instanceDecl(instance));
    try Resolve.bindTypeParams(&typer, instance, &buffer);
    const resolved = try typer.aliasTarget(comp.instanceDecl(instance));
    comp.instancePtr(instance).type = resolved;
    return resolved != .poison;
}

fn aliasTarget(typer: *Typer, decl_index: Decl.Index) Allocator.Error!Pool.Index {
    const view = typer.tree.viewOf(typer.declNode(decl_index)).alias_decl;
    return Resolve.resolveWrittenType(typer, view.aliased);
}

pub fn topLevelLet(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var typer = context(comp, decl_index);
    const decl = comp.declAt(decl_index);
    const view = typer.tree.viewOf(decl.node).var_decl;

    // the annotation first, so a literal can land on what it says
    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try Resolve.resolveType(&typer, type_expr)
    else
        null;

    var value = try typer.checkValue(view.init_expr, annotation);
    assert(value != .runtime);
    assert(value != .diverged);
    if (annotation) |wanted| value = try typer.coerce(value, wanted, view.init_expr);

    const met: Pool.Index = if (value == .constant) value.constant else .poison;
    comp.declPtr(decl_index).answer = .{ .constant = met };
    typer.answerType(decl.node, met);
    return met != .poison;
}

pub fn declBounds(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var typer = context(comp, decl_index);
    const decl = comp.declAt(decl_index);
    const params = Resolve.typeParamNodes(comp, decl_index)[1];
    assert(params.len == decl.type_params);
    for (params, 0..) |param, at| {
        typer.link(param, .{ .local = param });
        const bound = try Resolve.boundOf(&typer, decl_index, param);
        comp.bounds.items[decl.bounds + at] = bound orelse .poison;
    }
    return true;
}

pub fn structRows(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    var typer = context(comp, decl_index);
    try Resolve.bindTypeParams(&typer, instance, &buffer);
    typer.demand_embedding = false;

    // staged, because resolving a field type can build other rows
    const mark = comp.scratch.rows.items.len;
    defer comp.scratch.rows.shrinkRetainingCapacity(mark);

    var clean = true;
    for (typer.tree.viewOf(typer.declNode(decl_index)).struct_decl.members) |member| {
        if (typer.tree.nodeTag(member) != .field) continue;
        const field = typer.tree.viewOf(member).field;
        const field_type = try Resolve.resolveType(&typer, field.type_expr);
        if (field_type == .poison) clean = false;
        typer.answerType(member, field_type);
        try typer.stageRow(field.name_token, field_type, member);
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
    var typer = context(comp, decl_index);
    const view = typer.tree.viewOf(typer.declNode(decl_index)).fn_decl;

    if (typer.module.space != .std) {
        try typer.failToken(view.name_token, .{
            .code = .builtin_outside_std,
            .message = "only the standard library declares an 'extern fn'",
            .label = "not available here",
            .help = "std wraps one in an ordinary function, so call that instead",
        });
        return false;
    }
    if (view.type_params.len > 0) {
        try typer.failToken(view.name_token, .{
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
    var typer = context(comp, decl_index);
    try Resolve.bindTypeParams(&typer, instance, &buffer);

    const view = typer.tree.viewOf(typer.declNode(decl_index)).fn_decl;

    // staged, because resolving a parameter type can build other rows
    const mark = comp.scratch.rows.items.len;
    defer comp.scratch.rows.shrinkRetainingCapacity(mark);

    var clean = true;
    for (view.params) |param_node| {
        if (typer.tree.nodeTag(param_node) != .param) continue;
        const param = typer.tree.viewOf(param_node).param;
        const name_text = typer.tree.tokenSlice(param.name_token);

        const param_type = try Resolve.resolveWrittenType(&typer, param.type_expr);
        if (param_type == .poison) clean = false;
        typer.answerType(param_node, param_type);
        typer.link(param_node, .{ .local = param_node });

        for (comp.scratch.rows.items[mark..]) |earlier| {
            if (comp.pool.sameText(earlier.name, name_text) == false) continue;
            try typer.fail(param_node, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is already a parameter", .{name_text}),
                .label = "declared again here",
                .notes = try typer.noteHere(earlier.node, "first declared here"),
            });
            clean = false;
            break;
        }
        if (view.is_extern) {
            if (try typer.externCrosses(param_node, param_type, "parameter") == false) clean = false;
        }
        try typer.stageRow(param.name_token, param_type, param_node);
    }
    try commitRows(comp, instance, mark);

    var return_type: Pool.Index = .void_type;
    if (view.return_type.unwrap()) |type_expr| {
        return_type = try Resolve.resolveWrittenType(&typer, type_expr);
        if (view.is_extern) {
            if (try typer.externCrosses(type_expr, return_type, "return type") == false) clean = false;
        }
    }
    comp.instancePtr(instance).type = return_type;
    return clean and return_type != .poison;
}

fn stageRow(
    typer: *Typer,
    name_token: Token.Index,
    type_index: Pool.Index,
    node: Node.Index,
) Allocator.Error!void {
    const comp = typer.comp;
    try comp.scratch.rows.append(comp.gpa, .{
        .name = try comp.pool.string(comp.gpa, typer.tree.tokenSlice(name_token)),
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
    typer: *Typer,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
) Allocator.Error!bool {
    const comp = typer.comp;
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

    try typer.fail(node, .{
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
    var typer = context(comp, decl_index);
    try Resolve.bindTypeParams(&typer, instance, &buffer);

    const marks = comp.scratch.mark();
    const builder = try comp.scratch.takeBuilder(comp.gpa);
    defer comp.scratch.releaseBuilder(builder);

    builder.instance = instance;
    builder.return_type = comp.instanceType(instance);
    builder.current = .entry;
    builder.defer_loops_floor = 0;
    builder.in_defer = false;
    builder.reachable = true;
    typer.builder = builder;
    try builder.insts.ensureTotalCapacity(comp.gpa, 64);

    const view = typer.tree.viewOf(typer.declNode(decl_index)).fn_decl;
    assert(view.is_extern == false);
    const body_node = view.body.unwrap() orelse return false;
    if (typer.tree.nodeTag(body_node) != .block) return false;

    const entry = try typer.newBlock();
    assert(entry == .entry);
    typer.startBlock(entry);

    const rows = comp.instanceRows(instance);
    try builder.locals.ensureTotalCapacity(comp.gpa, rows.len + 8);
    for (rows) |row| {
        const param_ref = try typer.emit(row.node, .param, row.type, .{ .name = row.name });
        try typer.declareLocal(row.name, row.node, .param, param_ref, row.type);
    }

    _ = try typer.checkBlockValue(body_node, .void_type);
    if (typer.blockOpen()) {
        if (builder.reachable and builder.return_type != .void_type) {
            try typer.failToken(view.name_token, .{
                .code = .missing_return,
                .message = try comp.fmt("not every path through '{s}' returns its {s}", .{
                    comp.pool.stringText(comp.declAt(decl_index).name),
                    try comp.typeName(builder.return_type),
                }),
                .label = "a path falls off the end",
                .help = "every path must end in 'return', or loop forever",
            });
        }
        typer.endBlock(.{ .ret = .none });
    }
    assert(builder.scopes.items.len == 0);
    // every gather site restores its mark, nothing outlives the body
    assert(std.meta.eql(comp.scratch.mark(), marks));

    try typer.finishFunc();
    return true;
}

fn context(comp: *Compilation, decl_index: Decl.Index) Typer {
    const decl = comp.declAt(decl_index);
    const module = comp.moduleAt(decl.module);
    return .{
        .comp = comp,
        .module_index = decl.module,
        .module = module,
        .tree = module.tree,
        .bindings = &.{},
        .builder = null,
        .narrows_floor = @intCast(comp.scratch.narrows.items.len),
        .bool_type = .poison,
        .none_type = .poison,
        .demand_embedding = true,
    };
}

fn declNode(typer: *const Typer, decl_index: Decl.Index) Node.Index {
    const decl = typer.comp.declAt(decl_index);
    assert(decl.module == typer.module_index);
    return decl.node;
}

pub fn mainTokenText(typer: *const Typer, node: Node.Index) []const u8 {
    return typer.tree.tokenSlice(typer.tree.nodeMainToken(node));
}

pub fn origin(typer: *const Typer, node: Node.Index) Compilation.Origin {
    return .{ .module = typer.module_index, .node = node };
}

pub fn body(typer: *const Typer) *Builder {
    return typer.builder orelse unreachable;
}

pub fn pointerTo(typer: *Typer, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    return comp.pool.intern(comp.gpa, .{ .type_pointer = .{ .child = child, .mutable = mutable } });
}

pub fn sliceOf(typer: *Typer, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    return comp.pool.intern(comp.gpa, .{ .type_slice = .{ .child = child, .mutable = mutable } });
}

pub fn emit(
    typer: *Typer,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    data: IR.Inst.Data,
) Allocator.Error!Ref {
    const builder = typer.body();
    assert(node.int() < typer.tree.nodes.len);
    try typer.reopenDead();

    if (builder.insts.len >= IR.Ref.inst_count_max) return error.OutOfMemory;
    const index: IR.Inst.Index = .from(builder.insts.len);
    try builder.insts.append(typer.comp.gpa, .{
        .tag = tag,
        .type = type_index,
        .node = node,
        .data = data,
    });
    return .fromInst(index);
}

pub fn emitOne(
    typer: *Typer,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    operand: Ref,
) Allocator.Error!Ref {
    assert(operand != .none);
    return typer.emit(node, tag, type_index, .{ .un = operand });
}

pub fn emitValue(
    typer: *Typer,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    data: IR.Inst.Data,
) Allocator.Error!Value {
    return runtimeValue(try typer.emit(node, tag, type_index, data), type_index);
}

pub fn emitOneValue(
    typer: *Typer,
    node: Node.Index,
    tag: IR.Inst.Tag,
    type_index: Pool.Index,
    operand: Ref,
) Allocator.Error!Value {
    return runtimeValue(try typer.emitOne(node, tag, type_index, operand), type_index);
}

pub fn emitSlot(
    typer: *Typer,
    node: Node.Index,
    name: Pool.String,
    value_type: Pool.Index,
) Allocator.Error!Ref {
    const slot_type = try typer.pointerTo(value_type, true);
    return typer.emit(node, .local, slot_type, .{ .name = name });
}

pub fn emitStore(typer: *Typer, node: Node.Index, place: Ref, value: Ref) Allocator.Error!void {
    assert(place != .none);
    assert(value != .none);
    _ = try typer.emit(node, .store, .void_type, .{ .bin = .{ .lhs = place, .rhs = value } });
}

pub fn emitExtra(
    typer: *Typer,
    header: []const u32,
    operands: []const Operand,
) Allocator.Error!IR.ExtraIndex {
    const builder = typer.body();
    if (builder.extra.items.len + header.len + operands.len > std.math.maxInt(u32)) {
        return error.OutOfMemory;
    }

    const start: u32 = @intCast(builder.extra.items.len);
    try builder.extra.ensureUnusedCapacity(typer.comp.gpa, header.len + operands.len);
    builder.extra.appendSliceAssumeCapacity(header);
    for (operands) |operand| {
        const ref = refOf(operand.value);
        assert(ref != .none);
        builder.extra.appendAssumeCapacity(@intFromEnum(ref));
    }
    return @enumFromInt(start);
}

pub fn newBlock(typer: *Typer) Allocator.Error!IR.Block.Index {
    const builder = typer.body();
    if (builder.blocks.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: IR.Block.Index = .from(builder.blocks.items.len);
    try builder.blocks.append(typer.comp.gpa, .{ .first = 0, .count = 0, .terminator = null });
    return index;
}

pub fn startBlock(typer: *Typer, block: IR.Block.Index) void {
    const builder = typer.body();
    const opened = builder.blockAt(block);
    assert(opened.terminator == null);
    opened.first = @intCast(builder.insts.len);
    builder.current = block;
}

pub fn endBlock(typer: *Typer, terminator: IR.Terminator) void {
    const builder = typer.body();
    const block = builder.currentBlock();
    assert(block.terminator == null);
    block.count = @as(u32, @intCast(builder.insts.len)) - block.first;
    block.terminator = terminator;
}

pub fn blockOpen(typer: *const Typer) bool {
    return typer.body().currentBlock().terminator == null;
}

/// Closes the block with a jump, and says whether anything reachable flowed out.
pub fn jumpTo(typer: *Typer, target: IR.Block.Index) bool {
    if (typer.blockOpen() == false) return false;
    const flowed = typer.body().reachable;
    typer.endBlock(.{ .jump = target });
    return flowed;
}

pub fn trap(typer: *Typer) Allocator.Error!void {
    try typer.reopenDead();
    typer.endBlock(.trap);
}

/// A closed block gets an unreachable successor, so what follows still checks.
pub fn reopenDead(typer: *Typer) Allocator.Error!void {
    const builder = typer.body();
    if (builder.currentBlock().terminator == null) return;
    typer.startBlock(try typer.newBlock());
    builder.reachable = false;
    assert(typer.blockOpen());
}

pub fn pushScope(typer: *Typer) Allocator.Error!void {
    const builder = typer.body();
    try builder.scopes.append(typer.comp.gpa, .{
        .locals_start = @intCast(builder.locals.items.len),
        .defers_start = @intCast(builder.defer_nodes.items.len),
    });
}

pub fn popScope(typer: *Typer) void {
    const builder = typer.body();
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
pub fn unwindScopesTo(typer: *Typer, target: u32) Allocator.Error!void {
    const builder = typer.body();
    assert(target <= builder.scopes.items.len);

    var index = builder.scopes.items.len;
    var defers_end = builder.defer_nodes.items.len;
    while (index > target) {
        index -= 1;
        const scope = builder.scopes.items[index];
        var defer_index = defers_end;
        while (defer_index > scope.defers_start) {
            defer_index -= 1;
            try typer.emitDefer(builder.defer_nodes.items[defer_index]);
        }
        defers_end = scope.defers_start;
    }
}

fn emitDefer(typer: *Typer, node: Node.Index) Allocator.Error!void {
    const builder = typer.body();
    const outer = builder.in_defer;
    const floor = builder.defer_loops_floor;

    builder.in_defer = true;
    builder.defer_loops_floor = @intCast(builder.loops.items.len);
    defer {
        builder.in_defer = outer;
        builder.defer_loops_floor = floor;
    }
    try typer.checkStatement(node);
}

pub fn declareLocal(
    typer: *Typer,
    name: Pool.String,
    node: Node.Index,
    kind: Builder.Local.Kind,
    ref: Ref,
    type_index: Pool.Index,
) Allocator.Error!void {
    const builder = typer.body();
    const comp = typer.comp;
    const text = comp.pool.stringText(name);

    const clash: ?Diagnostic.Report = clash: {
        if (builder.names.get(name)) |other| break :clash .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is already in scope", .{text}),
            .label = "shadows the outer one",
            .notes = try typer.noteHere(typer.localAt(other).node, "first bound here"),
        };
        for (typer.bindings) |binding| {
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
        if (typer.module.findDecl(text)) |decl_index| break :clash .{
            .code = .shadows,
            .message = try comp.fmt("'{s}' is already declared in this file", .{text}),
            .label = "shadows it",
            .notes = try typer.noteHere(comp.declAt(decl_index).node, "declared here"),
        };
        break :clash null;
    };
    if (clash) |report| try typer.fail(node, report);

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

pub fn declarePoisoned(typer: *Typer, name: Pool.String, node: Node.Index) Allocator.Error!void {
    try typer.declareLocal(name, node, .let, broken_ref, .poison);
}

/// Past a handful the table wins, which keeps a body of thousands linear.
const scan_max = 32;

pub fn findLocalIndex(typer: *const Typer, text: []const u8) ?Builder.Local.Index {
    const builder = typer.builder orelse return null;
    const locals = builder.locals.items;

    if (locals.len > scan_max) {
        // declaring a local interns its name, so one nothing interned is no local
        const name = typer.comp.pool.lookupString(text) orelse return null;
        return builder.names.get(name);
    }
    var index = locals.len;
    while (index > 0) {
        index -= 1;
        if (typer.comp.pool.sameText(locals[index].name, text)) return .from(index);
    }
    return null;
}

pub fn localAt(typer: *const Typer, index: Builder.Local.Index) Builder.Local {
    const builder = typer.body();
    assert(index.int() < builder.locals.items.len);
    return builder.locals.items[index.int()];
}

pub fn checkBlockValue(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(typer.tree.nodeTag(node) == .block);
    const comp = typer.comp;
    const statements = typer.tree.viewOf(node).block;

    const builder = typer.builder orelse return typer.constantBlock(node, hint);

    try typer.pushScope();
    const depth: u32 = @intCast(builder.scopes.items.len - 1);
    defer typer.popScope();

    const narrows_mark = comp.scratch.narrows.items.len;
    defer comp.scratch.narrows.shrinkRetainingCapacity(narrows_mark);

    var value: Value = .void_value;
    for (statements, 0..) |statement, position| {
        if (typer.blockOpen() == false or builder.reachable == false) {
            if (position > 0) try typer.fail(statement, .{
                .code = .unreachable_code,
                .message = "this cannot be reached",
                .label = "never runs",
                .notes = try typer.noteHere(statements[position - 1], "the block already left here"),
            });
            break;
        }
        const tail = position + 1 == statements.len;
        if (tail and wantsValue(hint) and tagIsStatement(typer.tree.nodeTag(statement)) == false) {
            value = try typer.checkExpr(statement, hint);
        } else {
            try typer.checkStatement(statement);
        }
    }

    if (typer.blockOpen() == false or builder.reachable == false) return .diverged;
    try typer.unwindScopesTo(depth);
    return value;
}

fn constantBlock(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(typer.builder == null);
    const statements = typer.tree.viewOf(node).block;

    if (statements.len == 0) return .void_value;
    if (statements.len == 1 and tagIsStatement(typer.tree.nodeTag(statements[0])) == false) {
        return typer.checkExpr(statements[0], hint);
    }
    return typer.needRuntime(node, "a block that holds statements");
}

fn tagIsStatement(tag: Node.Tag) bool {
    return switch (tag) {
        .var_decl, .assign, .defer_stmt, .err => true,
        else => false,
    };
}

fn checkStatement(typer: *Typer, node: Node.Index) Allocator.Error!void {
    assert(typer.builder != null);
    switch (typer.tree.viewOf(node)) {
        .var_decl => try typer.checkVarDecl(node),
        .assign => |assign| try typer.checkAssign(node, assign),
        .defer_stmt => |deferred| try typer.body().defer_nodes.append(typer.comp.gpa, deferred),
        .err => |partial| if (partial.unwrap()) |kept| {
            _ = try typer.checkExpr(kept, null);
        },
        else => {
            const value = try typer.checkExpr(node, .void_type);
            if (typer.guardStatement(node)) |lhs| {
                const mark: u32 = @intCast(typer.comp.scratch.facts.items.len);
                defer typer.comp.scratch.facts.shrinkRetainingCapacity(mark);
                try Narrow.applyFacts(typer, (try Narrow.gatherFacts(typer, lhs)).when_true);
                return;
            }
            try typer.expectNothing(node, value);
        },
    }
}

/// `x is T or return`, whose left side holds for the rest of the block.
fn guardStatement(typer: *const Typer, node: Node.Index) ?Node.Index {
    if (typer.tree.nodeTag(node) != .binary) return null;
    const view = typer.tree.viewOf(node).binary;
    if (view.op != .bool_or) return null;
    return switch (typer.tree.nodeTag(view.rhs)) {
        .return_expr, .break_expr, .continue_expr => view.lhs,
        else => null,
    };
}

fn checkVarDecl(typer: *Typer, node: Node.Index) Allocator.Error!void {
    const comp = typer.comp;
    const view = typer.tree.viewOf(node).var_decl;
    const name_text = typer.tree.tokenSlice(view.name_token);

    if (Module.isDiscard(name_text)) return typer.failDiscard(node);
    const name = try comp.pool.string(comp.gpa, name_text);

    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try Resolve.resolveWrittenType(typer, type_expr)
    else
        null;

    var value = try typer.checkValue(view.init_expr, annotation);
    if (annotation) |wanted| value = try typer.coerce(value, wanted, view.init_expr);

    const value_type = typer.typeOf(value);
    if (value_type == .void_type) {
        try typer.fail(view.init_expr, .{
            .code = .type_mismatch,
            .message = "this produces nothing, so there is nothing to bind",
            .label = "no value here",
        });
        return typer.declarePoisoned(name, node);
    }
    if (value_type == .poison) return typer.declarePoisoned(name, node);

    if (view.is_mutable and value == .constant and Pool.isUntyped(value_type)) {
        assert(annotation == null);
        const example: ?[]const u8 = switch (comp.pool.keyOf(value.constant)) {
            .value_int => "i64",
            .value_float => "f64",
            .value_aggregate => |it| try comp.fmt("[{d}]{s}", .{
                it.elems.len,
                try Aggregate.elementExample(typer, it),
            }),
            else => null,
        };
        if (example) |shape| {
            try typer.fail(node, .{
                .code = .var_needs_type,
                .message = try comp.fmt("'{s}' needs a type before it can vary", .{name_text}),
                .label = "no type to hold it",
                .help = try comp.fmt("write 'var {s}: {s} = ...', or whichever type is meant", .{
                    name_text, shape,
                }),
            });
            return typer.declarePoisoned(name, node);
        }
    }

    typer.answer(node, value);
    typer.link(node, .{ .local = node });
    if (view.is_mutable) {
        const slot = try typer.emitSlot(node, name, value_type);
        try typer.emitStore(node, slot, refOf(value));
        return typer.declareLocal(name, node, .var_slot, slot, value_type);
    }
    try typer.declareLocal(name, node, .let, refOf(value), value_type);
}

fn checkAssign(typer: *Typer, node: Node.Index, assign: AST.View.Assign) Allocator.Error!void {
    if (assign.op == null and typer.tree.nodeTag(assign.lhs) == .ident) {
        if (Module.isDiscard(typer.mainTokenText(assign.lhs))) {
            _ = try typer.checkValue(assign.rhs, null);
            return;
        }
    }

    const place = try Place.checkPlace(typer, assign.lhs) orelse {
        _ = try typer.checkExpr(assign.rhs, null);
        return;
    };
    if (place.immutable) |why| {
        try Place.reportImmutable(typer, assign.lhs, place, why);
        _ = try typer.checkExpr(assign.rhs, place.type);
        return;
    }
    assert(place.kind == .address);
    if (place.type == .poison) return;

    const value: Value = if (assign.op) |op| folded: {
        const held = try Place.placeValue(typer, place);
        const rhs = try typer.checkValue(assign.rhs, place.type);
        if (rhs.stops()) return;
        break :folded try Expr.combine(typer, .{
            .node = node,
            .op = op,
            .op_token = assign.op_token,
            .lhs = runtimeValue(held, place.type),
            .lhs_node = assign.lhs,
            .rhs = rhs,
            .rhs_node = assign.rhs,
        });
    } else try typer.checkExpr(assign.rhs, place.type);

    const met = try typer.coerce(value, place.type, assign.rhs);
    if (met == .poison) return;
    try typer.emitStore(node, place.ref, refOf(met));
}

pub fn checkExpr(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const value = try typer.checkExprKind(node, hint);
    typer.answer(node, value);
    return value;
}

fn checkExprKind(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    if (typer.builder == null) {
        if (runtimeOnly(typer.tree.nodeTag(node))) |what| return typer.needRuntime(node, what);
    }

    switch (typer.tree.viewOf(node)) {
        .builtin => return Builtin.notAValue(typer, node),
        .ident => return Expr.checkIdent(typer, node),
        .number_literal => return Expr.checkNumber(typer, node),
        .string_literal => return Expr.checkString(typer, node),
        .multiline_string => |view| return Expr.checkMultilineString(typer, view),
        .char_literal => return Expr.checkChar(typer, node),
        .block => return typer.checkBlockValue(node, hint),
        .if_expr => |view| return Flow.checkIf(typer, node, view, hint),
        .loop_expr => |view| return Flow.checkLoop(typer, node, view, hint),
        .match_expr => |view| return Flow.checkMatch(typer, node, view, hint),
        .return_expr => |operand| return Flow.checkReturn(typer, node, operand),
        .break_expr => |view| return Flow.checkBreak(typer, node, view),
        .continue_expr => |label| return Flow.checkContinue(typer, node, label),
        .binary => |view| return Expr.checkBinary(typer, node, view, hint),
        .unary => |view| return Expr.checkUnary(typer, node, view),
        .is_expr => |view| return Narrow.checkIs(typer, node, view),
        .or_bind => |view| return Flow.checkOrBind(typer, node, view, hint),
        .field_access => |view| return Expr.checkFieldAccess(typer, node, view),
        .deref => return Place.checkDeref(typer, node),
        .call => return Call.checkCall(typer, node, hint),
        .bracket => |view| return Aggregate.checkBracketExpr(typer, node, view),
        .struct_literal => return Aggregate.checkStructLiteral(typer, node, hint),
        .array_literal => return Aggregate.checkArrayLiteral(typer, node, hint),
        .array_type, .slice_type, .pointer_type, .union_type => {
            const resolved = try Resolve.resolveType(typer, node);
            return if (resolved == .poison) .poison else .{ .named_type = resolved };
        },
        .err => |partial| {
            if (partial.unwrap()) |kept| _ = try typer.checkExpr(kept, null);
            return .poison;
        },
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

pub fn checkValue(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const value = try typer.checkExpr(node, hint);
    return if (try typer.valueOnly(node, value)) value else .poison;
}

pub fn valueOnly(typer: *Typer, node: Node.Index, value: Value) Allocator.Error!bool {
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
    try typer.fail(node, report);
    return false;
}

pub fn expectNothing(typer: *Typer, node: Node.Index, value: Value) Allocator.Error!void {
    if (try typer.valueOnly(node, value) == false) return;
    const found = typer.typeOf(value);
    if (found == .void_type or found == .poison) return;

    try typer.fail(node, .{
        .code = .value_unused,
        .message = if (typer.typeCanHold(found))
            try typer.comp.fmt("this {s} goes nowhere", .{try typer.comp.typeName(found)})
        else
            "this value goes nowhere",
        .label = "unused value",
        .help = "bind it, return it, or drop it with '_ ='",
    });
}

pub fn needRuntime(typer: *Typer, node: Node.Index, what: []const u8) Allocator.Error!Value {
    assert(typer.builder == null);
    return typer.refuse(node, .{
        .code = .not_constant,
        .message = try typer.comp.fmt(
            "this must settle before anything runs, and {s} happens at run time",
            .{what},
        ),
        .label = "not a constant",
        .help = "the constant set is literals, names of constants, operators, and parentheses",
    });
}

pub fn typeOf(typer: *const Typer, value: Value) Pool.Index {
    return switch (value) {
        .constant => |constant| typer.comp.pool.typeOfValue(constant),
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

pub fn untypedInt(typer: *Typer, value: i128) Allocator.Error!Value {
    return .{ .constant = try typer.comp.pool.int(typer.comp.gpa, .untyped_int_type, value) };
}

pub fn typeCanHold(typer: *const Typer, type_index: Pool.Index) bool {
    if (type_index == .void_type) return false;
    if (Pool.isUntyped(type_index)) return false;
    return typer.comp.pool.isType(type_index);
}

pub fn wantsValue(hint: ?Pool.Index) bool {
    const wanted = hint orelse return true;
    return wanted != .void_type;
}

/// Two unit members, the first meaning yes. `bool` is declared, never built in.
pub fn boolType(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    if (typer.bool_type == .poison) typer.bool_type = try typer.preludeType(node, .bool);
    return typer.bool_type;
}

pub fn noneType(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    if (typer.none_type == .poison) typer.none_type = try typer.preludeType(node, .none);
    return typer.none_type;
}

fn preludeType(
    typer: *Typer,
    node: Node.Index,
    which: enum { bool, none },
) Allocator.Error!Pool.Index {
    const pool = &typer.comp.pool;
    const name = switch (which) {
        .bool => Module.bool_name,
        .none => Module.none_name,
    };
    if (Resolve.visibleDecl(typer, name)) |decl_index| {
        const found = try Resolve.declAsType(typer, decl_index, node);
        const shaped = switch (which) {
            .bool => pool.isUnion(found) and pool.unionMemberCount(found) == 2 and
                pool.keyOf(pool.unionMemberAt(found, 0)) == .type_unit and
                pool.keyOf(pool.unionMemberAt(found, 1)) == .type_unit,
            .none => pool.keyOf(found) == .type_unit,
        };
        if (shaped) return found;
    }
    try typer.fail(node, switch (which) {
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

pub fn settledTruth(typer: *Typer, node: Node.Index, holds: bool) Allocator.Error!Value {
    const bools = try typer.boolType(node);
    return .{ .constant = try typer.comp.pool.truth(typer.comp.gpa, bools, holds) };
}

pub fn truthOf(typer: *const Typer, bools: Pool.Index, constant: Pool.Index) ?bool {
    if (bools == .poison) return null;
    const pool = &typer.comp.pool;
    const found = pool.memberOfValue(constant);
    if (found == pool.unionMemberAt(bools, 0)) return true;
    if (found == pool.unionMemberAt(bools, 1)) return false;
    return null;
}

/// What `node` settled as, which is a constant's value or a runtime value's type.
pub fn answer(typer: *Typer, node: Node.Index, value: Value) void {
    typer.module.record(node, switch (value) {
        .constant => |constant| constant,
        .runtime => |runtime| runtime.type,
        .named_type => |type_index| type_index,
        .diverged, .poison, .named_generic, .named_fn, .named_module => return,
    });
}

pub fn answerType(typer: *Typer, node: Node.Index, type_index: Pool.Index) void {
    typer.module.record(node, type_index);
}

pub fn link(typer: *Typer, node: Node.Index, symbol: Module.Symbol) void {
    typer.module.bind(node, symbol);
}

pub fn linkField(
    typer: *Typer,
    node: Node.Index,
    owner: Pool.Instance,
    row: Compilation.Row.Index,
) void {
    typer.link(node, .{ .field = .{
        .owner = typer.comp.instanceDecl(owner),
        .node = typer.comp.rowAt(row).node,
    } });
}

pub fn coerce(
    typer: *Typer,
    value: Value,
    wanted: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    if (wanted == .poison) return .poison;

    switch (value) {
        .poison => return .poison,
        .diverged => return .diverged,
        .constant => |constant| return typer.fitValue(constant, wanted, node),
        .runtime => |runtime| {
            if (runtime.type == wanted) return value;
            if (runtime.type == .poison) return .poison;

            if (Pool.widens(runtime.type, wanted)) {
                return typer.emitOneValue(node, .widen, wanted, runtime.ref);
            }
            if (writesThrough(&comp.pool, runtime.type, wanted)) |writable| {
                if (writable) return runtimeValue(runtime.ref, wanted);
                try typer.failNeedsWritable(node, runtime.type, wanted);
                return .poison;
            }
            if (comp.pool.isUnion(wanted)) {
                if (comp.pool.subsumes(wanted, runtime.type)) {
                    return typer.emitValue(node, .union_init, wanted, .{
                        .probe = .{ .operand = runtime.ref, .member = runtime.type },
                    });
                }
                if (unionMemberFor(&comp.pool, wanted, runtime.type)) |member| {
                    // membership settles the second step, so it cannot come back here
                    const met = try typer.coerce(value, member, node);
                    if (met == .poison) return .poison;
                    return typer.coerce(met, wanted, node);
                }
            }
            return typer.reportMismatch(node, value, wanted);
        },
        else => {
            _ = try typer.valueOnly(node, value);
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
    typer: *Typer,
    node: Node.Index,
    found: Pool.Index,
    wanted: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    const comp = typer.comp;
    try typer.fail(node, .{
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
    typer: *Typer,
    constant: Pool.Index,
    wanted: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    if (constant == .poison or wanted == .poison) return .poison;
    return switch (try comp.pool.fit(comp.gpa, constant, wanted, .allowed)) {
        .value => |final| .{ .constant = final },
        .does_not_fit => fitted: {
            try typer.fail(node, try typer.doesNotFit(constant, wanted, "an untyped constant " ++
                "takes any type its value fits, and this value does not fit this one"));
            break :fitted .poison;
        },
        .wrong_kind => try typer.reportMismatch(node, .{ .constant = constant }, wanted),
    };
}

pub fn doesNotFit(
    typer: *Typer,
    constant: Pool.Index,
    wanted: Pool.Index,
    help: ?[]const u8,
) Allocator.Error!Diagnostic.Report {
    return .{
        .code = .does_not_fit,
        .message = try typer.comp.fmt("{s} does not fit in {s}", .{
            try typer.comp.spellValue(constant),
            try typer.comp.typeName(wanted),
        }),
        .label = "past the type's edge",
        .help = help,
    };
}

fn reportMismatch(
    typer: *Typer,
    node: Node.Index,
    value: Value,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    const found = typer.typeOf(value);

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

    return typer.refuse(node, .{
        .code = if (narrowable) .not_narrowed else .type_mismatch,
        .message = try comp.fmt("expected {s}, found {s}", .{
            try comp.typeName(wanted),
            try comp.typeName(found),
        }),
        .label = "the wrong type",
        .help = help,
    });
}

pub fn fail(typer: *Typer, node: Node.Index, report: Diagnostic.Report) Allocator.Error!void {
    try typer.comp.reportNode(typer.module_index, node, report);
}

pub fn failToken(
    typer: *Typer,
    token: Token.Index,
    report: Diagnostic.Report,
) Allocator.Error!void {
    try typer.comp.reportToken(typer.module_index, token, report);
}

pub fn refuse(typer: *Typer, node: Node.Index, report: Diagnostic.Report) Allocator.Error!Value {
    try typer.fail(node, report);
    return .poison;
}

pub fn refuseToken(
    typer: *Typer,
    token: Token.Index,
    report: Diagnostic.Report,
) Allocator.Error!Value {
    try typer.failToken(token, report);
    return .poison;
}

pub fn noteHere(
    typer: *Typer,
    node: Node.Index,
    message: []const u8,
) Allocator.Error![]Diagnostic.Note {
    return typer.comp.noteOne(typer.module_index, node, message);
}

pub fn failDiscard(typer: *Typer, node: Node.Index) Allocator.Error!void {
    try typer.fail(node, .{
        .code = .discard_reserved,
        .message = "'_' is not a name, and only discards a value",
        .label = "not a name",
        .help = "write '_ = expression' to drop a value on purpose",
    });
}

pub fn reportUndefined(typer: *Typer, node: Node.Index, text: []const u8) Allocator.Error!void {
    try typer.fail(node, .{
        .code = .undefined_name,
        .message = try typer.comp.fmt("nothing named '{s}' is in scope here", .{text}),
        .label = "unknown name",
        .help = try typer.suggestName(text),
    });
}

fn suggestName(typer: *Typer, text: []const u8) Allocator.Error!?[]const u8 {
    const comp = typer.comp;
    var closest: Closest = .{ .target = text };

    if (typer.builder) |builder| {
        for (builder.locals.items) |local| closest.consider(comp.pool.stringText(local.name));
    }
    for (typer.bindings) |binding| closest.consider(comp.pool.stringText(binding.name));
    considerDecls(comp, &closest, typer.module.decls);
    if (comp.prelude) |prelude| {
        if (prelude != typer.module_index) considerDecls(comp, &closest, comp.moduleAt(prelude).decls);
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
    typer: *Typer,
    node: Node.Index,
    name: []const u8,
    of: Arguments,
    wanted: u64,
    written: usize,
    notes: []const Diagnostic.Note,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = switch (of) {
            .value => .wrong_arity,
            .type => .generic_arguments,
        },
        .message = switch (of) {
            .value => try typer.comp.fmt("'{s}' takes {d} argument{s}, and this call has {d}", .{
                name, wanted, plural(wanted), written,
            }),
            .type => try typer.comp.fmt("'{s}' takes {d} type argument{s}, and this writes {d}", .{
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

// a map slot holds one of these until the numbering pass replaces it with a number
const block_dead = std.math.maxInt(u32);
const block_live = block_dead - 1;

fn finishFunc(typer: *Typer) Allocator.Error!void {
    const comp = typer.comp;
    const gpa = comp.gpa;
    const builder = typer.body();
    const block_count = builder.blocks.items.len;
    assert(block_count > 0);
    assert(builder.block_map.items.len == 0);
    assert(builder.frontier.items.len == 0);

    try builder.block_map.appendNTimes(gpa, block_dead, block_count);
    try builder.frontier.ensureTotalCapacity(gpa, block_count);

    const map = builder.block_map.items;
    map[0] = block_live;
    builder.frontier.appendAssumeCapacity(0);
    while (builder.frontier.pop()) |raw| {
        switch (builder.blocks.items[raw].ended()) {
            .jump => |target| reach(map, &builder.frontier, target),
            .branch => |branch| {
                reach(map, &builder.frontier, branch.then_block);
                reach(map, &builder.frontier, branch.else_block);
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
        const terminator = block.ended();
        comp.ir.blocks.appendAssumeCapacity(.{
            .first = block.first,
            .count = block.count,
            .terminator = switch (terminator) {
                .jump => |target| .{ .jump = numbered(map, target) },
                .branch => |branch| .{ .branch = .{
                    .cond = branch.cond,
                    .then_block = numbered(map, branch.then_block),
                    .else_block = numbered(map, branch.else_block),
                } },
                .ret, .trap => terminator,
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
    const tree_nodes = typer.tree.nodes.len;
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

fn reach(map: []u32, frontier: *std.ArrayList(u32), block: IR.Block.Index) void {
    const slot = &map[block.int()];
    if (slot.* != block_dead) return;
    slot.* = block_live;
    frontier.appendAssumeCapacity(block.int());
}

/// A live block's successors are live, which is what the walk above settled.
fn numbered(map: []const u32, block: IR.Block.Index) IR.Block.Index {
    assert(map[block.int()] != block_dead);
    return @enumFromInt(map[block.int()]);
}

const testing = std.testing;

fn findNode(comp: *const Compilation, tag: Node.Tag, text: []const u8) Node.Index {
    const tree = comp.treeOf(.root);
    var raw: u32 = 0;
    while (raw < tree.nodes.len) : (raw += 1) {
        const node: Node.Index = .from(raw);
        if (tree.nodeTag(node) != tag) continue;
        if (std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), text)) return node;
    }
    unreachable; // a test names a node its own source holds
}

test "the checker records what every node settled as, and what every name refers to" {
    const gpa = testing.allocator;

    var sources: Source.Cache = .init(gpa, testing.io);
    defer sources.deinit();
    _ = try sources.overlay("case.phi",
        \\type Point = {
        \\    x: i64
        \\}
        \\
        \\fn area(p: Point) i64 {
        \\    let scaled = p.x * 2
        \\    return scaled
        \\}
        \\
    );

    var comp: Compilation = undefined;
    try comp.init(gpa, testing.io, &sources, .{
        .root_path = "case.phi",
        .std_dir = null,
        .target = .host,
    });
    defer comp.deinit();
    try comp.compile();
    try testing.expectEqual(0, comp.diagnostics.items.len);

    const module = comp.moduleAt(.root);
    const bound = findNode(&comp, .var_decl, "let");
    const used = findNode(&comp, .ident, "scaled");
    const receiver = findNode(&comp, .ident, "p");
    const read = findNode(&comp, .field_access, ".");

    // the type of an expression is data, not something only lowering ever saw
    for ([_]Node.Index{ bound, used, read }) |node| {
        try testing.expectEqualStrings("i64", try comp.typeName(module.answerOf(node)));
    }
    try testing.expectEqualStrings("Point", try comp.typeName(module.answerOf(receiver)));

    // a name and its declaration answer the same symbol, from either side
    const param = findNode(&comp, .param, "p");
    const point = module.findDecl("Point").?;
    const field = findNode(&comp, .field, "x");
    try testing.expectEqual(Module.Symbol{ .local = bound }, module.symbolOf(bound));
    try testing.expectEqual(Module.Symbol{ .local = bound }, module.symbolOf(used));
    try testing.expectEqual(Module.Symbol{ .local = param }, module.symbolOf(param));
    try testing.expectEqual(Module.Symbol{ .local = param }, module.symbolOf(receiver));
    try testing.expectEqual(Module.Symbol{ .decl = point }, module.symbolOf(findNode(&comp, .ident, "Point")));
    try testing.expectEqual(
        Module.Symbol{ .field = .{ .owner = point, .node = field } },
        module.symbolOf(read),
    );
}

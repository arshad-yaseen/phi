//! Type-checks a declaration, lowering each function body to IR as it goes.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const Comptime = @import("Comptime.zig");
const Diagnostic = @import("Diagnostic.zig");
const Handle = @import("Handle.zig");
const IR = @import("IR.zig");
const Layout = @import("Layout.zig");
const Literal = @import("Literal.zig");
const Module = @import("Module.zig");
const Pool = @import("Pool.zig");
const Builtin = @import("Builtin.zig").Builtin;
const Token = @import("Token.zig");

const Closest = Compilation.Closest;
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
/// Field types skip the embedding demand, because their struct gets its own walk.
demand_embedding: bool,

const Check = @This();

fn body(check: *const Check) *Builder {
    return check.builder orelse unreachable;
}

const type_params_max = AST.type_params_max;
const bindings_max = type_params_max * 2;
pub const call_args_max = 255;
const type_depth_max = AST.nest_max;

const Binding = struct { name: Pool.String, type: Pool.Index, bound: ?Pool.Index };

/// What `refOf` answers for a value that already reported, so it stays silent.
const broken_ref: Ref = .fromConstant(.poison);

pub const Operand = struct { value: Value, initializer: Node.OptionalIndex };

/// A `named_` case is not a value.
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

    /// Callers read the type, never the ref.
    const void_value: Value = .{
        .runtime = .{ .ref = .fromConstant(.poison), .type = .void_type },
    };

    /// Poison has reported, and diverged has left.
    pub fn stops(value: Value) bool {
        return value == .poison or value == .diverged;
    }
};

pub fn typeAlias(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const resolved = try check.aliasTarget(decl_index);
    comp.declPtr(decl_index).result = resolved.int();
    return resolved != .poison;
}

pub fn aliasInstance(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, comp.instanceDecl(instance));
    try check.bindTypeParams(instance, &buffer);
    const resolved = try check.aliasTarget(comp.instanceDecl(instance));
    comp.instancePtr(instance).type = resolved;
    return resolved != .poison;
}

fn aliasTarget(check: *Check, decl_index: Decl.Index) Allocator.Error!Pool.Index {
    const view = check.tree.viewOf(check.declNode(decl_index)).alias_decl;
    return check.resolveWrittenType(view.aliased);
}

pub fn topLevelLet(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index);
    const view = check.tree.viewOf(check.declNode(decl_index)).var_decl;

    // the annotation first, so a literal can land on what it says
    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try check.resolveType(type_expr)
    else
        null;

    var value = try check.checkValue(view.init_expr, annotation);
    // constants-only mode never emits, and nothing there can leave
    assert(value != .runtime);
    assert(value != .diverged);
    if (annotation) |wanted| value = try check.coerce(value, wanted, view.init_expr);

    const met: Pool.Index = if (value == .constant) value.constant else .poison;
    comp.declPtr(decl_index).result = met.int();
    return met != .poison;
}

pub fn structRows(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try check.bindTypeParams(instance, &buffer);
    check.demand_embedding = false;

    // staged, because resolving a field type can build other rows
    const mark = comp.rows_scratch.items.len;
    defer comp.rows_scratch.shrinkRetainingCapacity(mark);

    var clean = true;
    for (check.tree.viewOf(check.declNode(decl_index)).struct_decl.members) |member| {
        if (check.tree.nodeTag(member) != .field) continue;
        const field = check.tree.viewOf(member).field;
        const field_type = try check.resolveType(field.type_expr);
        if (field_type == .poison) clean = false;
        try check.stageRow(field.name_token, field_type, member);
    }
    try commitRows(comp, instance, mark);
    return clean;
}

fn stageRow(
    check: *Check,
    name_token: Token.Index,
    type_index: Pool.Index,
    node: Node.Index,
) Allocator.Error!void {
    const comp = check.comp;
    try comp.rows_scratch.append(comp.gpa, .{
        .name = try comp.pool.string(comp.gpa, check.tree.tokenSlice(name_token)),
        .type = type_index,
        .node = node,
    });
}

fn commitRows(comp: *Compilation, instance: Pool.Instance, mark: usize) Allocator.Error!void {
    const staged = comp.rows_scratch.items[mark..];
    if (comp.rows.items.len + staged.len > std.math.maxInt(u32)) return error.OutOfMemory;

    const rows_start: u32 = @intCast(comp.rows.items.len);
    try comp.rows.appendSlice(comp.gpa, staged);
    comp.instancePtr(instance).rows = .since(rows_start, comp.rows.items.len);
}

/// What a struct embeds by value. A cycle means no size, which `ensure` reports.
pub fn structEmbedding(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl = comp.declAt(comp.instanceDecl(instance));
    try comp.ensure(.of(.rows, instance), .{ .module = decl.module, .node = decl.node });

    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        // by index, because the walk can grow the rows table
        const row = comp.rowAt(.from(raw));
        try walkEmbedded(comp, row.type, .{ .module = decl.module, .node = row.node }, 0);
    }
    return true;
}

fn walkEmbedded(
    comp: *Compilation,
    type_index: Pool.Index,
    from: Compilation.Origin,
    depth: u32,
) Allocator.Error!void {
    if (depth >= type_depth_max) return;
    switch (comp.pool.typeKey(type_index)) {
        .type_struct => |embedded| try comp.ensure(.of(.embedding, embedded), from),
        // every element embeds, so an array of a type is a cycle through it
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

pub fn fnSignature(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try check.bindTypeParams(instance, &buffer);

    const view = check.tree.viewOf(check.declNode(decl_index)).fn_decl;

    // staged, because resolving a parameter type can build other rows
    const mark = comp.rows_scratch.items.len;
    defer comp.rows_scratch.shrinkRetainingCapacity(mark);

    var clean = true;
    for (view.params) |param_node| {
        if (check.tree.nodeTag(param_node) != .param) continue;
        const param = check.tree.viewOf(param_node).param;
        const name_text = check.tree.tokenSlice(param.name_token);

        const param_type = try check.resolveWrittenType(param.type_expr);
        if (param_type == .poison) clean = false;

        for (comp.rows_scratch.items[mark..]) |earlier| {
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
            const crosses = try check.externCrosses(param_node, param_type, "parameter");
            if (crosses == false) clean = false;
        }
        try check.stageRow(param.name_token, param_type, param_node);
    }
    try commitRows(comp, instance, mark);

    var return_type: Pool.Index = .void_type;
    if (view.return_type.unwrap()) |type_expr| {
        return_type = try check.resolveWrittenType(type_expr);
        if (view.is_extern) {
            const crosses = try check.externCrosses(type_expr, return_type, "return type");
            if (crosses == false) clean = false;
        }
    }
    comp.instancePtr(instance).type = return_type;
    return clean and return_type != .poison;
}

fn typeParamNodes(comp: *const Compilation, decl_index: Decl.Index) [2][]const Node.Index {
    const decl = comp.declAt(decl_index);
    const tree = comp.treeOf(decl.module);
    return .{
        if (decl.owner.unwrap()) |owner_index|
            tree.viewOf(comp.declAt(owner_index).node).struct_decl.type_params
        else
            &.{},
        switch (tree.viewOf(decl.node)) {
            .struct_decl => |view| view.type_params,
            .fn_decl => |view| view.type_params,
            .alias_decl => |view| view.type_params,
            else => &.{},
        },
    };
}

fn bindTypeParams(
    check: *Check,
    instance: Pool.Instance,
    buffer: *[bindings_max]Binding,
) Allocator.Error!void {
    const comp = check.comp;
    assert(check.bindings.len == 0);
    const args = comp.instanceArgs(instance);

    var count: u32 = 0;
    for (typeParamNodes(comp, comp.instanceDecl(instance))) |list| {
        assert(list.len <= type_params_max);
        for (list) |param| {
            assert(count < buffer.len);
            buffer[count] = .{
                .name = try comp.pool.string(comp.gpa, check.mainTokenText(param)),
                .type = args[count],
                .bound = try check.boundOf(comp.instanceDecl(instance), param),
            };
            count += 1;
        }
    }
    assert(count == args.len);
    check.bindings = buffer[0..count];
}

fn boundOf(check: *Check, decl_index: Decl.Index, param: Node.Index) Allocator.Error!?Pool.Index {
    assert(check.bindings.len == 0);
    // recovery can leave a hole where a parameter was, already reported
    if (check.tree.nodeTag(param) != .type_param) return null;
    const written = check.tree.viewOf(param).type_param.bound.unwrap() orelse return null;

    // a parameter is not concrete, and would otherwise be reported as unknown
    if (check.tree.nodeTag(written) == .ident) {
        for (typeParamNodes(check.comp, decl_index)) |list| {
            for (list) |other| {
                if (check.tree.nodeTag(other) != .type_param) continue;
                const other_name = check.mainTokenText(other);
                if (std.mem.eql(u8, other_name, check.mainTokenText(written)) == false) continue;
                try check.fail(written, .{
                    .code = .not_a_type,
                    .message = try check.comp.fmt("a bound names concrete types, and '{s}' " ++
                        "is a type parameter", .{other_name}),
                    .label = "not concrete",
                });
                return null;
            }
        }
    }

    const bound = try check.resolveType(written);
    return if (bound == .poison) null else bound;
}

fn unionBoundOfName(check: *const Check, node: Node.Index) ?Pool.Index {
    if (check.tree.nodeTag(node) != .ident) return null;
    const text = check.mainTokenText(node);
    for (check.bindings) |binding| {
        if (check.comp.pool.sameText(binding.name, text) == false) continue;
        const bound = binding.bound orelse return null;
        return if (check.comp.pool.isUnion(bound)) bound else null;
    }
    return null;
}

/// Whether the bound admits the type. A union bound admits its members, never a union.
fn withinBound(pool: *const Pool, bound: Pool.Index, type_index: Pool.Index) bool {
    if (pool.isUnion(bound)) return pool.unionHas(bound, type_index);
    return bound == type_index;
}

fn admittedBy(
    comp: *Compilation,
    bound: Pool.Index,
    hinted: Pool.Index,
    literal: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    const pool = &comp.pool;
    if (withinBound(pool, bound, hinted)) return hinted;
    if (pool.isUnion(hinted) == false) return null;

    var members = pool.membersOf(hinted);
    while (members.next()) |member| {
        if (withinBound(pool, bound, member) == false) continue;
        if (literal) |constant| {
            if (try pool.fit(comp.gpa, constant, member, .allowed) != .value) continue;
        }
        return member;
    }
    return null;
}

fn boundsHold(
    check: *Check,
    decl_index: Decl.Index,
    args: []const Pool.Index,
    node: Node.Index,
) Allocator.Error!bool {
    const comp = check.comp;
    const params = typeParamNodes(comp, decl_index)[1];
    assert(params.len == args.len);

    var callee = context(comp, decl_index);
    for (params, args) |param, arg| {
        const bound = try callee.boundOf(decl_index, param) orelse continue;
        if (withinBound(&comp.pool, bound, arg)) continue;
        try check.fail(node, .{
            .code = .not_a_member,
            .message = try comp.fmt("'{s}' is not a member of '{s}', which bounds '{s}'", .{
                try comp.typeName(arg),
                try comp.typeName(bound),
                callee.mainTokenText(param),
            }),
            .label = "outside the bound",
            .notes = try comp.noteOne(callee.module_index, param, "bounded here"),
        });
        return false;
    }
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
        .narrows_floor = @intCast(comp.narrows.items.len),
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

fn mainTokenText(check: *const Check, node: Node.Index) []const u8 {
    return check.tree.tokenSlice(check.tree.nodeMainToken(node));
}

/// A written type promises storage, so what it embeds must have a size.
pub fn resolveWrittenType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    const resolved = try check.resolveType(node);
    if (check.demand_embedding and resolved != .poison) {
        try walkEmbedded(check.comp, resolved, check.origin(node), 0);
    }
    return resolved;
}

fn resolveType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    switch (check.tree.viewOf(node)) {
        .ident => return check.resolveTypeName(node),
        .field_access => |access| switch (try check.checkExpr(access.lhs, null)) {
            .named_module => |target| {
                const member = try check.exported(target, node, access.name_token) orelse
                    return .poison;
                return check.declAsType(member, node);
            },
            .poison => return .poison,
            else => {
                try check.fail(node, .{
                    .code = .not_a_type,
                    .message = "only a module reaches a type with '.'",
                    .label = "not a type",
                });
                return .poison;
            },
        },
        .bracket => return check.resolveBracketType(node),
        .array_type => |array| return check.resolveArrayType(array),
        .slice_type => |slice| {
            const child = try check.resolveType(slice.child);
            if (child == .poison) return .poison;
            return check.sliceOf(child, slice.is_mutable);
        },
        .pointer_type => |pointer| {
            const child = try check.resolveType(pointer.child);
            if (child == .poison) return .poison;
            return check.pointerTo(child, pointer.is_mutable);
        },
        .union_type => |members| return check.resolveUnionType(node, members),
        .match_expr => if (try check.resolveMatchType(node)) |found| return found,
        .binary => |it| if (it.op == .bit_or) return check.resolveOrType(node, it),
        .err => return .poison,
        else => {},
    }
    try check.fail(node, .{
        .code = .not_a_type,
        .message = "this is a value, and a type belongs here",
        .label = "not a type",
    });
    return .poison;
}

/// A `match` that settles. One that does not picks a value, which the caller reports.
fn resolveMatchType(check: *Check, node: Node.Index) Allocator.Error!?Pool.Index {
    const chosen = try check.checkExpr(node, null);
    if (chosen.stops()) return .poison;
    return check.namedType(node, chosen);
}

pub fn pointerTo(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = check.comp;
    return comp.pool.intern(comp.gpa, .{ .type_pointer = .{ .child = child, .mutable = mutable } });
}

pub fn sliceOf(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = check.comp;
    return comp.pool.intern(comp.gpa, .{ .type_slice = .{ .child = child, .mutable = mutable } });
}

fn resolveArrayType(check: *Check, view: AST.View.ArrayType) Allocator.Error!Pool.Index {
    const comp = check.comp;
    const length = try check.arrayLength(view.length);
    const child = try check.resolveType(view.child);
    if (child == .poison) return .poison;
    const count = length orelse return .poison;
    return comp.pool.intern(comp.gpa, .{ .type_array = .{ .child = child, .len = count } });
}

fn arrayLength(check: *Check, node: Node.Index) Allocator.Error!?u64 {
    const value = try check.checkValue(node, .u64_type);
    if (value.stops()) return null;
    if (value == .runtime) {
        try check.fail(node, .{
            .code = .not_constant,
            .message = "an array's length is part of its type, so it is known " ++
                "before anything runs",
            .label = "not a constant",
            .help = "write the length itself, or another array's length",
        });
        return null;
    }

    const met = try check.fitValue(value.constant, .u64_type, node);
    if (met != .constant) return null;

    const folded = check.comp.pool.keyOf(met.constant).value_int;
    assert(folded.type == .u64_type);
    assert(folded.value >= 0);
    return @intCast(folded.value);
}

fn resolveUnionType(
    check: *Check,
    node: Node.Index,
    members: []const Node.Index,
) Allocator.Error!Pool.Index {
    assert(members.len >= 2);
    if (members.len > Pool.union_members_max) {
        try check.failTooWide(node);
        return .poison;
    }

    var buffer: [Pool.union_members_max]Pool.Index = undefined;
    var clean = true;
    for (members, 0..) |member, at| {
        buffer[at] = try check.resolveType(member);
        if (buffer[at] == .poison) clean = false;
    }
    if (clean == false) return .poison;
    return check.uniteResolved(node, buffer[0..members.len], members);
}

fn uniteResolved(
    check: *Check,
    node: Node.Index,
    resolved: []const Pool.Index,
    written: []const Node.Index,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    switch (try comp.pool.unite(comp.gpa, resolved)) {
        .index => |index| return index,
        .duplicate => |repeat| {
            var where = node;
            for (written, 0..) |member, at| {
                if (resolved[at] == repeat) where = member;
            }
            try check.fail(where, .{
                .code = .duplicate_member,
                .message = try comp.fmt("'{s}' is already a member of this union", .{
                    try comp.typeName(repeat),
                }),
                .label = "the same type again",
                .help = "members are distinct types, and an alias is not a new type",
            });
        },
        .too_wide => try check.failTooWide(node),
    }
    return .poison;
}

fn failGenericBare(check: *Check, node: Node.Index, name: []const u8) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .generic_arguments,
        .message = try check.comp.fmt("'{s}' is generic, so it needs its arguments", .{name}),
        .label = "no arguments here",
        .help = try check.comp.fmt("write '{s}[...]' with one type per parameter", .{name}),
    });
}

fn resolveOrType(
    check: *Check,
    node: Node.Index,
    it: AST.View.Binary,
) Allocator.Error!Pool.Index {
    assert(it.op == .bit_or);
    const lhs = try check.resolveType(it.lhs);
    const rhs = try check.resolveType(it.rhs);
    if (lhs == .poison or rhs == .poison) return .poison;
    return check.uniteResolved(node, &.{ lhs, rhs }, &.{});
}

fn failTooWide(check: *Check, node: Node.Index) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .union_too_wide,
        .message = try check.comp.fmt("flat, a union holds at most {d} members", .{
            Pool.union_members_max,
        }),
        .label = "too wide",
    });
}

fn resolveTypeName(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    const text = check.mainTokenText(node);
    for (check.bindings) |binding| {
        if (check.comp.pool.sameText(binding.name, text)) return binding.type;
    }
    if (Pool.primitiveType(text)) |primitive| return primitive;
    const decl_index = check.visibleDecl(text) orelse {
        try check.reportUndefined(node, text);
        return .poison;
    };
    return check.declAsType(decl_index, node);
}

fn visibleDecl(check: *const Check, text: []const u8) ?Decl.Index {
    if (check.module.findDecl(text)) |own| return own;

    const comp = check.comp;
    const prelude = comp.prelude orelse return null;
    if (prelude == check.module_index) return null;

    const found = comp.moduleAt(prelude).findDecl(text) orelse return null;
    if (Module.declIsPub(comp, found) == false) return null;
    return found;
}

fn exported(
    check: *Check,
    target: Module.Index,
    node: Node.Index,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    return Module.findExported(check.comp, target, check.origin(node), name_token);
}

fn ensured(check: *Check, decl_index: Decl.Index, node: Node.Index) Allocator.Error!?u32 {
    try check.comp.ensure(.forDecl(decl_index), check.origin(node));
    const decl = check.comp.declAt(decl_index);
    if (decl.state != .done) return null;
    return decl.result;
}

fn declAsType(check: *Check, decl_index: Decl.Index, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = check.comp;
    const decl = comp.declAt(decl_index);
    const name = comp.pool.stringText(decl.name);

    switch (decl.kind) {
        .struct_decl, .type_alias => {
            if (comp.typeParamCount(decl_index) > 0) {
                try check.failGenericBare(node, name);
                return .poison;
            }
            if (decl.kind == .struct_decl) {
                const instance = try comp.instantiate(decl_index, &.{}, check.origin(node));
                return comp.instanceType(instance);
            }
            const result = try check.ensured(decl_index, node) orelse return .poison;
            return @enumFromInt(result);
        },
        .unit_decl => {
            assert(comp.typeParamCount(decl_index) == 0);
            return comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
        },
        .import => {
            if (try check.ensured(decl_index, node) == null) return .poison;
            try check.fail(node, .{
                .code = .not_a_type,
                .message = try comp.fmt("'{s}' is a module, not a type", .{name}),
                .label = "a module",
                .help = "name a type inside it",
            });
            return .poison;
        },
        .let, .fn_decl, .extern_fn => {
            const what: []const u8 = if (decl.kind == .let) "a value" else "a function";
            try check.fail(node, .{
                .code = .not_a_type,
                .message = try comp.fmt("'{s}' is {s}, not a type", .{ name, what }),
                .label = "not a type",
            });
            return .poison;
        },
    }
}

fn resolveBracketType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = check.comp;
    const view = check.tree.viewOf(node).bracket;

    const base = try check.checkExpr(view.base, null);
    const decl_index = switch (base) {
        .named_generic => |decl_index| decl_index,
        .named_type, .named_fn => {
            try check.fail(node, .{
                .code = .generic_arguments,
                .message = if (base == .named_type)
                    "this type takes no type arguments"
                else
                    "a function is not a type",
                .label = "arguments on the wrong thing",
            });
            return .poison;
        },
        .poison => return .poison,
        else => {
            try check.fail(view.base, .{
                .code = .not_a_type,
                .message = "only a generic struct takes type arguments here",
                .label = "not a generic type",
            });
            return .poison;
        },
    };

    const wanted = comp.typeParamCount(decl_index);
    if (view.args.len != wanted) {
        const name = comp.pool.stringText(comp.declAt(decl_index).name);
        try check.failArity(node, name, .type, wanted, view.args.len, &.{});
        return .poison;
    }

    var args_buffer: [type_params_max]Pool.Index = undefined;
    const args = args_buffer[0..view.args.len];
    for (view.args, args) |arg, *resolved| {
        resolved.* = try check.resolveType(arg);
        if (resolved.* == .poison) return .poison;
    }
    if (try check.boundsHold(decl_index, args, node) == false) return .poison;

    const instance = try comp.instantiate(decl_index, args, check.origin(node));
    if (comp.declAt(decl_index).kind == .type_alias) {
        try comp.ensure(.of(.alias, instance), check.origin(node));
        if (comp.instanceAt(instance).rows_state != .done) return .poison;
    }
    return comp.instanceType(instance);
}

pub const Builder = struct {
    instance: Pool.Instance = undefined,
    return_type: Pool.Index = undefined,
    insts: IR.InstList = .empty,
    extra: std.ArrayList(u32) = .empty,
    blocks: std.ArrayList(BlockBuild) = .empty,
    current: IR.Block.Index = undefined,
    locals: std.ArrayList(Local) = .empty,
    scopes: std.ArrayList(Scope) = .empty,
    defer_nodes: std.ArrayList(Node.Index) = .empty,
    loops: std.ArrayList(LoopFrame) = .empty,
    /// Scratch for `finishFunc`, retained across bodies.
    block_map: std.ArrayList(u32) = .empty,
    frontier: std.ArrayList(u32) = .empty,
    /// Loops below this are outside the `defer` being emitted.
    defer_loops_floor: u32 = undefined,
    in_defer: bool = undefined,
    /// Unreachable code is still checked, then dropped.
    reachable: bool = undefined,

    /// The terminator is null while the block is still open.
    const BlockBuild = struct {
        first: u32,
        count: u32,
        terminator: ?IR.Terminator,

        fn ended(block: BlockBuild) IR.Terminator {
            return block.terminator orelse unreachable;
        }
    };

    const Local = struct {
        name: Pool.String,
        node: Node.Index,
        kind: Kind,
        ref: Ref,
        /// A `var_slot` ref is a pointer to this.
        type: Pool.Index,

        const Kind = enum(u8) { let, var_slot, param };

        const Index = Handle.Index("local");
    };

    const Scope = struct { locals_start: u32, defers_start: u32 };

    const LoopFrame = struct {
        /// `.empty` when the loop has no label.
        label: Pool.String,
        node: Node.Index,
        /// The `continue` target, which re-reads the condition.
        header: IR.Block.Index,
        exit: IR.Block.Index,
        /// Scopes at entry. Leaving the loop unwinds down to here.
        scope_depth: u32,
        join: Join,
        broke_reachable: bool,
    };

    pub const empty: Builder = .{};

    fn blockAt(builder: *Builder, index: IR.Block.Index) *BlockBuild {
        assert(index.int() < builder.blocks.items.len);
        return &builder.blocks.items[index.int()];
    }

    fn currentBlock(builder: *Builder) *BlockBuild {
        return builder.blockAt(builder.current);
    }

    pub fn clear(builder: *Builder) void {
        inline for (@typeInfo(Builder).@"struct".fields) |field| {
            if (@typeInfo(field.type) == .@"struct") {
                @field(builder, field.name).clearRetainingCapacity();
            }
        }
    }

    pub fn deinit(builder: *Builder, gpa: Allocator) void {
        inline for (@typeInfo(Builder).@"struct".fields) |field| {
            if (@typeInfo(field.type) == .@"struct") @field(builder, field.name).deinit(gpa);
        }
        builder.* = undefined;
    }
};

pub fn fnBody(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    if (comp.instanceAt(instance).rows_state != .done) return false;

    var buffer: [bindings_max]Binding = undefined;
    var check = context(comp, decl_index);
    try check.bindTypeParams(instance, &buffer);

    const facts_mark = comp.facts.items.len;
    const narrows_mark = comp.narrows.items.len;

    const builder = try comp.takeBuilder();
    defer comp.releaseBuilder();

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
    // recovery can leave a hole where the body should be, already reported
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
    assert(comp.facts.items.len == facts_mark);
    assert(comp.narrows.items.len == narrows_mark);

    try check.finishFunc();
    return true;
}

fn emit(
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

fn emitSlot(
    check: *Check,
    node: Node.Index,
    name: Pool.String,
    value_type: Pool.Index,
) Allocator.Error!Ref {
    const slot_type = try check.pointerTo(value_type, true);
    return check.emit(node, .local, slot_type, .{ .name = name });
}

fn emitStore(check: *Check, node: Node.Index, place: Ref, value: Ref) Allocator.Error!void {
    assert(place != .none);
    assert(value != .none);
    _ = try check.emit(node, .store, .void_type, .{ .bin = .{ .lhs = place, .rhs = value } });
}

fn newBlock(check: *Check) Allocator.Error!IR.Block.Index {
    const builder = check.body();
    if (builder.blocks.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
    const index: IR.Block.Index = .from(builder.blocks.items.len);
    try builder.blocks.append(check.comp.gpa, .{ .first = 0, .count = 0, .terminator = null });
    return index;
}

fn startBlock(check: *Check, block: IR.Block.Index) void {
    const builder = check.body();
    const opened = builder.blockAt(block);
    assert(opened.terminator == null);
    opened.first = @intCast(builder.insts.len);
    builder.current = block;
}

fn endBlock(check: *Check, terminator: IR.Terminator) void {
    const builder = check.body();
    const block = builder.currentBlock();
    assert(block.terminator == null);
    block.count = @as(u32, @intCast(builder.insts.len)) - block.first;
    block.terminator = terminator;
}

fn blockOpen(check: *const Check) bool {
    return check.body().currentBlock().terminator == null;
}

fn jumpTo(check: *Check, target: IR.Block.Index) bool {
    if (check.blockOpen() == false) return false;
    const flowed = check.body().reachable;
    check.endBlock(.{ .jump = target });
    return flowed;
}

pub fn trap(check: *Check) Allocator.Error!void {
    try check.reopenDead();
    check.endBlock(.trap);
}

/// What follows a leave lands in a block nothing reaches, which `finishFunc` drops.
fn reopenDead(check: *Check) Allocator.Error!void {
    const builder = check.body();
    if (builder.currentBlock().terminator == null) return;
    check.startBlock(try check.newBlock());
    builder.reachable = false;
    assert(check.blockOpen());
}

fn pushScope(check: *Check) Allocator.Error!void {
    const builder = check.body();
    try builder.scopes.append(check.comp.gpa, .{
        .locals_start = @intCast(builder.locals.items.len),
        .defers_start = @intCast(builder.defer_nodes.items.len),
    });
}

fn popScope(check: *Check) void {
    const builder = check.body();
    const scope = builder.scopes.getLast();
    builder.scopes.shrinkRetainingCapacity(builder.scopes.items.len - 1);
    builder.locals.shrinkRetainingCapacity(scope.locals_start);
    builder.defer_nodes.shrinkRetainingCapacity(scope.defers_start);
}

/// Defers in reverse, innermost scope down to `target`. Every way out goes through here.
fn unwindScopesTo(check: *Check, target: u32) Allocator.Error!void {
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

fn declareLocal(
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
        for (builder.locals.items) |other| {
            if (other.name != name) continue;
            break :clash .{
                .code = .shadows,
                .message = try comp.fmt("'{s}' is already in scope", .{text}),
                .label = "shadows the outer one",
                .notes = try check.noteHere(other.node, "first bound here"),
            };
        }
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
    try builder.locals.append(comp.gpa, .{
        .name = name,
        .node = node,
        .kind = kind,
        .ref = ref,
        .type = type_index,
    });
}

fn findLocalIndex(check: *const Check, name: []const u8) ?Builder.Local.Index {
    const builder = check.builder orelse return null;
    var index = builder.locals.items.len;
    while (index > 0) {
        index -= 1;
        if (check.comp.pool.sameText(builder.locals.items[index].name, name)) return .from(index);
    }
    return null;
}

fn localAt(check: *const Check, index: Builder.Local.Index) Builder.Local {
    const builder = check.body();
    assert(index.int() < builder.locals.items.len);
    return builder.locals.items[index.int()];
}

fn loopPtr(check: *Check, index: usize) *Builder.LoopFrame {
    const builder = check.body();
    assert(index < builder.loops.items.len);
    return &builder.loops.items[index];
}

fn activeNarrow(check: *const Check, name: Name) ?Narrow {
    const narrows = check.comp.narrows.items;
    assert(narrows.len >= check.narrows_floor);
    var index = narrows.len;
    while (index > check.narrows_floor) {
        index -= 1;
        if (std.meta.eql(narrows[index].name, name)) return narrows[index];
    }
    return null;
}

fn checkBlockValue(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(check.tree.nodeTag(node) == .block);
    const comp = check.comp;
    const statements = check.tree.viewOf(node).block;

    const builder = check.builder orelse return check.constantBlock(node, hint);

    try check.pushScope();
    const depth: u32 = @intCast(builder.scopes.items.len - 1);
    defer check.popScope();

    const narrows_mark = comp.narrows.items.len;
    defer comp.narrows.shrinkRetainingCapacity(narrows_mark);

    var value: Value = .void_value;
    for (statements, 0..) |statement, position| {
        if (check.blockOpen() == false or builder.reachable == false) {
            if (position > 0) {
                const left_at = statements[position - 1];
                try check.fail(statement, .{
                    .code = .unreachable_code,
                    .message = "this cannot be reached",
                    .label = "never runs",
                    .notes = try check.noteHere(left_at, "the block already left here"),
                });
            }
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

/// Where nothing runs, a block is the one expression it holds.
fn constantBlock(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(check.builder == null);
    const statements = check.tree.viewOf(node).block;

    if (statements.len == 0) return .void_value;
    if (statements.len == 1) {
        switch (check.tree.nodeTag(statements[0])) {
            .var_decl, .assign, .defer_stmt => {},
            else => return check.checkExpr(statements[0], hint),
        }
    }
    return check.needRuntime(node, "a block that holds statements");
}

/// The one arm a settled `if` or `match` enters, and the whole of what it is.
fn checkChosen(
    check: *Check,
    arm: Node.OptionalIndex,
    proved: Compilation.Range,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const narrows_mark = comp.narrows.items.len;
    defer comp.narrows.shrinkRetainingCapacity(narrows_mark);

    try check.applyFacts(proved);
    const taken = arm.unwrap() orelse return .void_value;

    const value = try check.checkExpr(taken, hint);
    if (wantsValue(hint)) return value;
    try check.expectNothing(taken, value);
    return if (value == .diverged) .diverged else .void_value;
}

/// An `if` with no `else` has an edge that skips the arm, so what follows is reached.
fn fallsPast(check: *Check) Allocator.Error!void {
    // only an arm that left reaches here, and leaving takes a body
    const builder = check.body();
    const reached = builder.reachable;
    check.startBlock(try check.newBlock());
    builder.reachable = reached;
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
                const mark: u32 = @intCast(check.comp.facts.items.len);
                defer check.comp.facts.shrinkRetainingCapacity(mark);
                try check.applyFacts((try check.gatherFacts(lhs)).when_true);
                return;
            }
            try check.expectNothing(node, value);
        },
    }
}

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
        try check.resolveWrittenType(type_expr)
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
                try check.elementExample(it),
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

fn elementExample(check: *Check, aggregate: Pool.Key.Aggregate) Allocator.Error![]const u8 {
    if (aggregate.elems.len == 0) return "u32";
    const found = check.comp.pool.typeOfValue(aggregate.elems[0]);
    if (Pool.isUntyped(found)) return "u32";
    return check.comp.typeName(found);
}

fn declarePoisoned(check: *Check, name: Pool.String, node: Node.Index) Allocator.Error!void {
    try check.declareLocal(name, node, .let, broken_ref, .poison);
}

fn checkAssign(check: *Check, node: Node.Index, assign: AST.View.Assign) Allocator.Error!void {
    if (assign.op == null and check.tree.nodeTag(assign.lhs) == .ident) {
        if (Module.isDiscard(check.mainTokenText(assign.lhs))) {
            _ = try check.checkValue(assign.rhs, null);
            return;
        }
    }

    const place = try check.checkPlace(assign.lhs) orelse {
        _ = try check.checkExpr(assign.rhs, null);
        return;
    };
    if (place.immutable) |why| {
        try check.reportImmutable(assign.lhs, place, why);
        _ = try check.checkExpr(assign.rhs, place.type);
        return;
    }
    assert(place.kind == .address);
    if (place.type == .poison) return;

    const value: Value = if (assign.op) |op| folded: {
        const held = try check.placeValue(place);
        const rhs = try check.checkValue(assign.rhs, place.type);
        if (rhs.stops()) return;
        break :folded try check.combine(.{
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

fn checkIf(
    check: *Check,
    node: Node.Index,
    view: AST.View.If,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;

    const wants = wantsValue(hint);
    if (wants and view.else_node == .none) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this 'if' has no 'else', so one path through it produces nothing",
            .label = "needs an 'else'",
            .help = "an 'if' used as a value says what it is on every path",
        });
    }

    const cond = try check.checkCondition(view.cond);
    if (cond == broken_ref) return .poison;

    const facts_mark: u32 = @intCast(comp.facts.items.len);
    defer comp.facts.shrinkRetainingCapacity(facts_mark);
    const facts = try check.gatherFacts(view.cond);

    if (check.conditionTruth(cond)) |truth| {
        const taken = if (truth) view.then_block.toOptional() else view.else_node;
        const proved = if (truth) facts.when_true else facts.when_false;
        const value = try check.checkChosen(taken, proved, hint);

        // one edge reaches past the 'if', so what that edge proved still holds
        if (value != .diverged) {
            try check.applyFacts(proved);
            return value;
        }
        if (view.else_node != .none) return value;

        // no 'else', so the edge that skips the arm is what reaches past it
        assert(truth);
        try check.fallsPast();
        try check.applyFacts(facts.when_false);
        return .void_value;
    }

    // a condition that neither settled nor broke had to run, so a body is building
    const builder = check.body();
    const carries = wants and view.else_node != .none;
    var join = try Join.open(check, "if", node, carries, hint, node.toOptional());

    const then_block = try check.newBlock();
    const else_block = try check.newBlock();
    const join_block = try check.newBlock();

    try check.reopenDead();
    const entry_reachable = builder.reachable;
    check.endBlock(.{ .branch = .{
        .cond = cond,
        .then_block = then_block,
        .else_block = else_block,
    } });

    const narrows_mark = comp.narrows.items.len;

    check.startBlock(then_block);
    builder.reachable = entry_reachable;
    try check.applyFacts(facts.when_true);
    const then_value = try check.checkExpr(view.then_block, hint);
    comp.narrows.shrinkRetainingCapacity(narrows_mark);
    try join.take(check, then_value, view.then_block);
    var join_reachable = check.jumpTo(join_block);

    check.startBlock(else_block);
    builder.reachable = entry_reachable;
    var else_value: Value = .diverged;
    if (view.else_node.unwrap()) |else_node| {
        try check.applyFacts(facts.when_false);
        else_value = try check.checkExpr(else_node, hint);
        comp.narrows.shrinkRetainingCapacity(narrows_mark);
        try join.take(check, else_value, else_node);
        if (check.jumpTo(join_block)) join_reachable = true;
    } else {
        if (entry_reachable) join_reachable = true;
        check.endBlock(.{ .jump = join_block });
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    // only one branch falls through, so its facts keep holding past the if
    if (then_value == .diverged and (view.else_node == .none or else_value != .diverged)) {
        try check.applyFacts(facts.when_false);
    }
    if (then_value != .diverged and view.else_node != .none and else_value == .diverged) {
        try check.applyFacts(facts.when_true);
    }
    return join.close(check, then_value == .diverged and else_value == .diverged);
}

/// Where the arms of an `if`, a loop, or a `match` leave their value.
const Join = struct {
    /// The keyword, for the message when nothing says what type this is.
    what: []const u8,
    /// The `if`, loop, or `match` the slot belongs to.
    node: Node.Index,
    /// `.none` for a statement, where the arms produce nothing.
    slot: Ref,
    result_type: Pool.Index,
    carries: bool,
    settled: bool,
    /// Who the message blames, where it is not the arm itself.
    names_type: Node.OptionalIndex,

    fn open(
        check: *Check,
        what: []const u8,
        node: Node.Index,
        carries: bool,
        hint: ?Pool.Index,
        names_type: Node.OptionalIndex,
    ) Allocator.Error!Join {
        return .{
            .what = what,
            .node = node,
            .slot = if (carries) try check.emitSlot(node, .empty, hint orelse .poison) else .none,
            .result_type = hint orelse .poison,
            .carries = carries,
            .settled = hint != null,
            .names_type = names_type,
        };
    }

    fn armHint(join: Join) ?Pool.Index {
        if (join.carries == false) return .void_type;
        return if (join.settled) join.result_type else null;
    }

    /// An arm's value into the slot, where an untyped one waits for the first arm with a type.
    fn take(join: *Join, check: *Check, value: Value, at: Node.Index) Allocator.Error!void {
        if (join.carries == false) return;
        if (value == .diverged) return;
        if (try check.valueOnly(at, value) == false) return;

        if (join.settled == false) {
            const found = check.typeOf(value);
            if (value == .constant and Pool.isUntyped(found)) {
                return check.emitStore(at, join.slot, refOf(value));
            }
            const blamed = join.names_type.unwrap() orelse at;
            join.result_type = try check.settleType(blamed, found, join.what);
            join.settled = true;
        }
        const met = try check.coerce(value, join.result_type, at);
        try check.emitStore(at, join.slot, refOf(met));
    }

    /// What the arms left behind. The slot is typed even where nothing reads it.
    fn close(join: Join, check: *Check, diverged: bool) Allocator.Error!Value {
        if (join.carries == false) return .void_value;
        // a slot no arm typed holds a byte, which nothing reads
        try check.setSlotType(join.slot, if (join.settled) join.result_type else .u8_type);
        try join.settleWaiting(check);

        if (diverged) return .diverged;
        if (join.result_type == .poison) return .poison;
        return check.emitOneValue(join.node, .load, join.result_type, join.slot);
    }

    fn settleWaiting(join: Join, check: *Check) Allocator.Error!void {
        const builder = check.body();
        const pool = &check.comp.pool;
        const tags = builder.insts.items(.tag);
        const data = builder.insts.items(.data);
        const nodes = builder.insts.items(.node);

        // the slot was emitted first, so its stores all follow it
        var at = join.slot.unwrap().inst.int() + 1;
        while (at < builder.insts.len) : (at += 1) {
            if (tags[at] != .store) continue;
            if (data[at].bin.lhs != join.slot) continue;
            const constant = switch (data[at].bin.rhs.unwrap()) {
                .constant => |constant| constant,
                .inst => continue,
            };
            if (Pool.isUntyped(pool.typeOfValue(constant)) == false) continue;

            if (join.settled == false) {
                const blamed = join.names_type.unwrap() orelse nodes[at];
                _ = try check.settleType(blamed, pool.typeOfValue(constant), join.what);
                return;
            }
            const met = try check.fitValue(constant, join.result_type, nodes[at]);
            data[at].bin.rhs = refOf(met);
        }
    }
};

fn settleType(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    if (found == .poison) return .poison;
    if (check.typeCanHold(found)) return found;

    if (found == .void_type) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = try comp.fmt("this produces nothing, and the '{s}' needs a value", .{what}),
            .label = "no value here",
        });
    } else {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = try comp.fmt("nothing says what type this '{s}' is", .{what}),
            .label = "no type in sight",
            .help = try comp.fmt("annotate what it feeds, as in 'let n: i64 = {s} ...'", .{what}),
        });
    }
    return .poison;
}

fn loopLabel(check: *Check, token: ?Token.Index) Allocator.Error!Pool.String {
    const comp = check.comp;
    const named = token orelse return .empty;

    const text = check.tree.tokenSlice(named);
    const label = try comp.pool.string(comp.gpa, text);
    for (check.body().loops.items) |other| {
        if (other.label != label) continue;
        try check.failToken(named, .{
            .code = .shadows,
            .message = try comp.fmt("':{s}' already names an enclosing loop", .{text}),
            .label = "shadows it",
            .notes = try check.noteHere(other.node, "first labeled here"),
        });
        break;
    }
    return label;
}

/// The header re-reads the condition per pass, and exits go through the frame this pushes.
fn checkLoop(
    check: *Check,
    node: Node.Index,
    view: AST.View.Loop,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const builder = check.body();
    assert(check.tree.nodeTag(node) == .loop_expr);

    // recovery can leave a hole where the body should be, already reported
    if (check.tree.nodeTag(view.body) != .block) return .poison;

    try check.reopenDead();

    const carries = wantsValue(hint);
    const else_missing = carries and view.head.ends() and view.else_node == .none;
    if (else_missing) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this loop has no 'else', so it has no value when it ends on its own",
            .label = "needs an 'else'",
            .help = "a loop used as a value says what it is when it ends on its own",
        });
    }

    var join = try Join.open(check, "loop", node, carries, hint, .none);
    const label = try check.loopLabel(view.label);

    const counting: ?AST.View.LoopRange = switch (view.head) {
        .range => |it| it,
        .forever, .cond => null,
    };
    const counter: ?Counter = if (counting) |it| try check.startCounter(it.name, it.over) else null;
    try check.reopenDead();

    const header = try check.newBlock();
    const body_block = try check.newBlock();
    const exit = try check.newBlock();
    const else_target: IR.Block.Index = if (view.else_node != .none) try check.newBlock() else exit;
    // increment gets its own block so `continue` hits it before the test
    const latch: IR.Block.Index = if (counter != null) try check.newBlock() else header;

    check.endBlock(.{ .jump = header });
    check.startBlock(header);
    const holds: ?Ref = switch (view.head) {
        .forever => null,
        .cond => |cond_node| asked: {
            const cond = try check.checkCondition(cond_node);
            try check.reopenDead();
            break :asked cond;
        },
        .range => try check.counterBelowEnd(counter),
    };
    const runs = builder.reachable;
    if (holds) |cond| {
        check.endBlock(.{ .branch = .{
            .cond = cond,
            .then_block = body_block,
            .else_block = else_target,
        } });
    } else {
        check.endBlock(.{ .jump = body_block });
    }

    try builder.loops.append(comp.gpa, .{
        .label = label,
        .node = node,
        .header = latch,
        .exit = exit,
        .scope_depth = @intCast(builder.scopes.items.len),
        .join = join,
        .broke_reachable = false,
    });

    check.startBlock(body_block);
    builder.reachable = runs;
    if (counting) |it| try check.bindCounter(it.name, counter);
    _ = try check.checkBlockValue(view.body, .void_type);
    if (counting != null) check.popScope();
    if (check.blockOpen()) check.endBlock(.{ .jump = latch });

    if (counter) |it| {
        check.startBlock(latch);
        try check.countOn(it);
        check.endBlock(.{ .jump = header });
    }

    const finished = builder.loops.getLast();
    builder.loops.shrinkRetainingCapacity(builder.loops.items.len - 1);
    join = finished.join;

    var else_flows = false;
    if (view.else_node.unwrap()) |else_node| {
        check.startBlock(else_target);
        builder.reachable = runs and view.head.ends();
        if (view.head.ends() == false) {
            try check.fail(else_node, .{
                .code = .unreachable_code,
                .message = "this 'else' never runs, because a loop with no " ++
                    "condition never ends on its own",
                .label = "never runs",
            });
        }
        const else_value = try check.checkExpr(else_node, join.armHint());
        try join.take(check, else_value, else_node);
        else_flows = check.jumpTo(exit);
    }

    check.startBlock(exit);
    const ends_here = if (view.else_node == .none) runs else else_flows;
    const exit_reachable = finished.broke_reachable or (view.head.ends() and ends_here);
    builder.reachable = exit_reachable;

    const value = try join.close(check, exit_reachable == false);
    return if (else_missing) .poison else value;
}

const Counter = struct {
    slot: Ref,
    /// Read once, before the first pass.
    end: Ref,
    type: Pool.Index,
    node: Node.Index,
};

fn startCounter(check: *Check, name: Node.Index, over: Node.Index) Allocator.Error!?Counter {
    const comp = check.comp;
    // recovery can leave a hole where the range should be, already reported
    if (check.tree.nodeTag(over) != .range_expr) return null;

    const range = check.tree.viewOf(over).range_expr;
    const end_node = range.end.unwrap() orelse return null;

    const first = try check.checkRangeEnd(range.start) orelse return null;
    const last = try check.checkRangeEnd(end_node) orelse return null;
    const ends = try check.settleEnds(
        over,
        .{ .value = first, .node = range.start },
        .{ .value = last, .node = end_node },
    ) orelse return null;
    if (try check.rangeRunsBackwards(over, ends.start, ends.end)) return null;

    const text = check.mainTokenText(name);
    const named: Pool.String = if (Module.isDiscard(text))
        .empty
    else
        try comp.pool.string(comp.gpa, text);
    const slot = try check.emitSlot(over, named, ends.type);
    try check.emitStore(over, slot, refOf(ends.start));
    return .{ .slot = slot, .end = refOf(ends.end), .type = ends.type, .node = over };
}

fn counterBelowEnd(check: *Check, counter: ?Counter) Allocator.Error!Ref {
    const it = counter orelse return broken_ref;
    const current = try check.emitOne(it.node, .load, it.type, it.slot);
    return check.emit(it.node, .cmp_lt, .void_type, .{ .bin = .{ .lhs = current, .rhs = it.end } });
}

fn bindCounter(check: *Check, name: Node.Index, counter: ?Counter) Allocator.Error!void {
    try check.pushScope();

    const text = check.mainTokenText(name);
    if (Module.isDiscard(text)) return check.failDiscard(name);
    const named = try check.comp.pool.string(check.comp.gpa, text);

    const it = counter orelse return check.declarePoisoned(named, name);
    const current = try check.emitOne(name, .load, it.type, it.slot);
    try check.declareLocal(named, name, .let, current, it.type);
}

fn countOn(check: *Check, counter: Counter) Allocator.Error!void {
    const comp = check.comp;
    const current = try check.emitOne(counter.node, .load, counter.type, counter.slot);
    const one = try comp.pool.int(comp.gpa, counter.type, 1);
    const next = try check.emit(counter.node, .add, counter.type, .{
        .bin = .{ .lhs = current, .rhs = .fromConstant(one) },
    });
    try check.emitStore(counter.node, counter.slot, next);
}

fn setSlotType(check: *Check, slot: Ref, value_type: Pool.Index) Allocator.Error!void {
    const builder = check.body();
    const index = slot.unwrap().inst.int();
    assert(builder.insts.items(.tag)[index] == .local);
    builder.insts.items(.type)[index] = try check.pointerTo(value_type, true);
}

const Subject = struct {
    /// The union the arms must cover, or null for an open set of types.
    set: ?Pool.Index,
    /// The member or type the scrutinee is settled as, or null where only running tells.
    held: ?Pool.Index,
    ref: Ref,
    /// The name the arms narrow, and the set they narrow it within.
    narrows: ?Narrows,

    const Narrows = struct { name: Name, set: Pool.Index };
};

fn matchSubject(check: *Check, scrutinee: Node.Index, value: Value) Allocator.Error!?Subject {
    const comp = check.comp;
    if (try check.namedType(scrutinee, value)) |named| {
        if (named == .poison) return null;
        return .{
            .set = check.unionBoundOfName(scrutinee),
            .held = named,
            .ref = broken_ref,
            .narrows = null,
        };
    }

    if (try check.valueOnly(scrutinee, value) == false) return null;
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (comp.pool.isUnion(found) == false) {
        try check.failNotUnion(scrutinee, found, "'match' asks which member a union holds");
        return null;
    }

    const narrows: ?Subject.Narrows = if (check.narrowedName(scrutinee)) |name|
        .{ .name = name, .set = found }
    else
        null;
    return .{
        .set = found,
        .held = if (value == .constant) comp.pool.memberOfValue(value.constant) else null,
        .ref = refOf(value),
        .narrows = narrows,
    };
}

fn narrowedName(check: *const Check, node: Node.Index) ?Name {
    if (check.tree.nodeTag(node) != .ident) return null;
    const text = check.mainTokenText(node);
    if (check.findLocalIndex(text)) |index| {
        if (check.localAt(index).kind == .var_slot) return null;
        return .{ .local = index };
    }
    const decl_index = check.visibleDecl(text) orelse return null;
    if (check.comp.declAt(decl_index).kind != .let) return null;
    return .{ .decl = decl_index };
}

fn nameType(check: *const Check, name: Name) Pool.Index {
    return switch (name) {
        .local => |index| check.localAt(index).type,
        .decl => |index| check.comp.pool.typeOfValue(check.declConstant(index)),
    };
}

fn nameRef(check: *const Check, name: Name) Ref {
    return switch (name) {
        .local => |index| check.localAt(index).ref,
        .decl => |index| .fromConstant(check.declConstant(index)),
    };
}

fn declConstant(check: *const Check, decl_index: Decl.Index) Pool.Index {
    const decl = check.comp.declAt(decl_index);
    assert(decl.kind == .let);
    if (decl.state != .done) return .poison;
    return @enumFromInt(decl.result);
}

/// Labels first, then one arm for a settled scrutinee, or a test per arm for a running one.
fn checkMatch(
    check: *Check,
    node: Node.Index,
    view: AST.View.Match,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .match_expr);

    const scrutinee = try check.checkExpr(view.scrutinee, null);

    const subject = try check.matchSubject(view.scrutinee, scrutinee) orelse {
        for (view.arms) |arm_node| {
            if (check.tree.nodeTag(arm_node) != .match_arm) continue;
            _ = try check.checkExpr(check.tree.viewOf(arm_node).match_arm.body, hint);
        }
        return .poison;
    };

    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);
    const labels = try check.matchLabels(node, view, subject);

    if (subject.held) |held| {
        const chosen = for (view.arms, 0..) |_, position| {
            if (comp.pool.covers(comp.pool.scratch.items[mark + position], held)) break position;
        } else labels.otherwise orelse {
            if (subject.set == null) try check.failToken(check.tree.nodeMainToken(node), .{
                .code = .missing_arm,
                .message = try comp.fmt("this match has no arm for '{s}'", .{
                    try comp.typeName(held),
                }),
                .label = "no arm names it",
                .help = "add an arm naming it, or 'else =>' for the rest",
            });
            return .poison;
        };

        const facts_mark: u32 = @intCast(comp.facts.items.len);
        defer comp.facts.shrinkRetainingCapacity(facts_mark);

        const arm_type = comp.pool.scratch.items[mark + chosen];
        if (subject.narrows) |narrows| {
            if (arm_type != .poison) try comp.facts.append(comp.gpa, .{
                .name = narrows.name,
                .type = arm_type,
                .node = view.arms[chosen],
            });
        }
        const proved: Compilation.Range = .{
            .start = facts_mark,
            .len = @intCast(comp.facts.items.len - facts_mark),
        };
        const arm = check.tree.viewOf(view.arms[chosen]).match_arm;
        return check.checkChosen(arm.body.toOptional(), proved, hint);
    }

    // a scrutinee that did not settle had to run, so a body is building
    const builder = check.body();
    try check.reopenDead();
    const entry_reachable = builder.reachable;
    const narrows_mark = comp.narrows.items.len;

    // the last arm skips its test, exhaustiveness makes it the fall-through
    const last = lastArm(check.tree, view.arms) orelse return .poison;

    var join = try Join.open(check, "match", node, wantsValue(hint), hint, .none);
    const join_block = try check.newBlock();
    var join_reachable = false;
    var all_diverged = true;

    for (view.arms, 0..) |arm_node, position| {
        if (check.tree.nodeTag(arm_node) != .match_arm) continue;
        const arm = check.tree.viewOf(arm_node).match_arm;
        const arm_type = comp.pool.scratch.items[mark + position];

        const arm_block = try check.newBlock();
        var resume_chain: ?IR.Block.Index = null;
        if (position == last) {
            check.endBlock(.{ .jump = arm_block });
        } else {
            const chain = try check.newBlock();
            if (arm_type == .poison) {
                check.endBlock(.{ .jump = chain });
            } else {
                // the compiler's own test, typed void, so no 'bool' is asked of the file
                const holds = try check.emit(arm_node, .union_is, .void_type, .{
                    .probe = .{ .operand = subject.ref, .member = arm_type },
                });
                check.endBlock(.{ .branch = .{
                    .cond = holds,
                    .then_block = arm_block,
                    .else_block = chain,
                } });
            }
            resume_chain = chain;
        }

        check.startBlock(arm_block);
        builder.reachable = entry_reachable;
        if (subject.narrows) |narrows| {
            if (arm_type != .poison) {
                try check.applyFact(.{ .name = narrows.name, .type = arm_type, .node = arm_node });
            }
        }
        const arm_value = try check.checkExpr(arm.body, join.armHint());
        comp.narrows.shrinkRetainingCapacity(narrows_mark);
        if (arm_value != .diverged) {
            all_diverged = false;
            try join.take(check, arm_value, arm.body);
            if (join.carries == false) try check.expectNothing(arm.body, arm_value);
        }

        if (check.jumpTo(join_block)) {
            join_reachable = true;
            if (arm_type != .poison) try comp.pool.scratch.append(comp.gpa, arm_type);
        }
        if (resume_chain) |chain| check.startBlock(chain);
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    // an arm that leaves narrows the code after the match, like a diverging branch
    if (subject.narrows) |narrows| {
        if (labels.clean and join_reachable) {
            const survivors = comp.pool.scratch.items[mark + view.arms.len ..];
            if (try check.membersWhere(narrows.set, survivors, .covered)) |kept| {
                if (kept != narrows.set) {
                    try check.applyFact(.{ .name = narrows.name, .type = kept, .node = node });
                }
            }
        }
    }
    return join.close(check, all_diverged);
}

const Labels = struct { otherwise: ?usize, clean: bool };

fn matchLabels(
    check: *Check,
    node: Node.Index,
    view: AST.View.Match,
    subject: Subject,
) Allocator.Error!Labels {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    var otherwise: ?usize = null;
    var clean = true;

    for (view.arms, 0..) |arm_node, position| {
        const arm_type: Pool.Index = blk: {
            // recovery can leave a hole where an arm was, already reported
            if (check.tree.nodeTag(arm_node) != .match_arm) break :blk .poison;
            const label_node = check.tree.viewOf(arm_node).match_arm.label.unwrap() orelse {
                // `else` takes whatever the arms before it left, so nothing may follow it
                if (otherwise != null) break :blk try check.failArmAfterElse(arm_node);
                otherwise = position;
                const set = subject.set orelse break :blk .poison;
                const earlier = comp.pool.scratch.items[mark..];
                break :blk try check.membersWhere(set, earlier, .uncovered) orelse {
                    try check.fail(arm_node, .{
                        .code = .duplicate_arm,
                        .message = "every member is already handled, so 'else' can never run",
                        .label = "nothing left for it",
                    });
                    break :blk .poison;
                };
            };
            const label = try check.resolveType(label_node);
            if (label == .poison) break :blk .poison;
            if (otherwise != null) break :blk try check.failArmAfterElse(label_node);
            if (subject.set) |set| {
                if (try check.labelWithin(label_node, label, set) == false) break :blk .poison;
            }
            if (try check.matchRepeat(view.arms, label_node, label, mark)) break :blk .poison;
            break :blk label;
        };
        if (arm_type == .poison) clean = false;
        try comp.pool.scratch.append(comp.gpa, arm_type);
    }

    // only a clean count can prove something was left out
    if (subject.set) |set| {
        if (clean) {
            const covered = comp.pool.scratch.items[mark..];
            if (try check.checkMatchMissing(node, set, covered)) clean = false;
        }
    }
    return .{ .otherwise = otherwise, .clean = clean };
}

fn coveredByAny(pool: *const Pool, sets: []const Pool.Index, member: Pool.Index) bool {
    for (sets) |set| if (pool.covers(set, member)) return true;
    return false;
}

fn membersWhere(
    check: *Check,
    set: Pool.Index,
    sets: []const Pool.Index,
    which: enum { covered, uncovered },
) Allocator.Error!?Pool.Index {
    const comp = check.comp;
    var kept: [Pool.union_members_max]Pool.Index = undefined;
    var count: u32 = 0;
    for (comp.pool.unionMembers(set)) |member| {
        if (coveredByAny(&comp.pool, sets, member) != (which == .covered)) continue;
        kept[count] = member;
        count += 1;
    }
    if (count == 0) return null;
    if (count == 1) return kept[0];
    return try comp.pool.intern(comp.gpa, .{ .type_union = kept[0..count] });
}

fn matchRepeat(
    check: *Check,
    arms: []const Node.Index,
    label_node: Node.Index,
    label: Pool.Index,
    mark: usize,
) Allocator.Error!bool {
    const comp = check.comp;
    const earlier = comp.pool.scratch.items[mark..];
    const named: []const Pool.Index = if (comp.pool.isUnion(label))
        comp.pool.unionMembers(label)
    else
        &.{label};

    for (named) |member| {
        for (earlier, 0..) |arm_type, position| {
            if (comp.pool.covers(arm_type, member) == false) continue;
            // one report per arm, however many members repeat
            const first = arms[position];
            const first_label = check.tree.viewOf(first).match_arm.label;
            try check.fail(label_node, .{
                .code = .duplicate_arm,
                .message = try comp.fmt("'{s}' is already handled by an earlier arm", .{
                    try comp.typeName(member),
                }),
                .label = "handled again here",
                .notes = try check.noteHere(first_label.unwrap() orelse first, "handled here"),
            });
            return true;
        }
    }
    return false;
}

fn lastArm(tree: *const AST, arms: []const Node.Index) ?usize {
    var index = arms.len;
    while (index > 0) {
        index -= 1;
        if (tree.nodeTag(arms[index]) == .match_arm) return index;
    }
    return null;
}

fn failArmAfterElse(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .duplicate_arm,
        .message = "'else' already takes every type the arms do not name",
        .label = "never runs",
    });
    return .poison;
}

fn checkMatchMissing(
    check: *Check,
    node: Node.Index,
    set: Pool.Index,
    covered: []const Pool.Index,
) Allocator.Error!bool {
    const comp = check.comp;

    const named_max = 5;
    var missing_count: u32 = 0;
    var names: []const u8 = "";
    for (comp.pool.unionMembers(set)) |member| {
        if (coveredByAny(&comp.pool, covered, member)) continue;
        missing_count += 1;
        if (missing_count > named_max) continue;
        names = try quotedList(comp, names, try comp.typeName(member));
    }
    if (missing_count == 0) return false;

    const message = if (missing_count > named_max)
        try comp.fmt("this match leaves out {s}, and {d} more members", .{
            names,
            missing_count - named_max,
        })
    else
        try comp.fmt("this match leaves out {s}", .{names});
    try check.failToken(check.tree.nodeMainToken(node), .{
        .code = .missing_arm,
        .message = message,
        .label = "not every member is handled",
        .help = "add an arm per member, or 'else =>' for the rest",
    });
    return true;
}

const Name = union(enum) { local: Builder.Local.Index, decl: Decl.Index };

/// What a condition proved about one name, on one edge.
pub const Fact = struct { name: Name, type: Pool.Index, node: Node.Index };

/// A fact in force, with the narrowed value the name reads as while it holds.
pub const Narrow = struct { name: Name, type: Pool.Index, ref: Ref };

/// What a condition proves about locals, per edge. Both are runs in `Builder.facts`.
const Facts = struct {
    when_true: Compilation.Range,
    when_false: Compilation.Range,

    const nothing: Facts = .{ .when_true = .empty, .when_false = .empty };
};

/// `is` proves a member when true, the rest when false. A failed `and` proves nothing.
fn gatherFacts(check: *Check, node: Node.Index) Allocator.Error!Facts {
    const comp = check.comp;
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            // marked after the call, which can grow the list under a mark taken first
            const found = try check.factsOfIs(node) orelse return .nothing;
            const start: u32 = @intCast(comp.facts.items.len);
            try comp.facts.append(comp.gpa, found.when_true);
            try comp.facts.append(comp.gpa, found.when_false);
            return .{
                .when_true = .{ .start = start, .len = 1 },
                .when_false = .{ .start = start + 1, .len = 1 },
            };
        },
        .binary => |it| {
            if (it.op != .bool_and) return .nothing;
            const start: u32 = @intCast(comp.facts.items.len);
            try check.gatherWhenTrue(node);
            const len: u32 = @intCast(comp.facts.items.len - start);
            return .{ .when_true = .{ .start = start, .len = len }, .when_false = .empty };
        },
        else => return .nothing,
    }
}

fn gatherWhenTrue(check: *Check, node: Node.Index) Allocator.Error!void {
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            const found = try check.factsOfIs(node) orelse return;
            try check.comp.facts.append(check.comp.gpa, found.when_true);
        },
        .binary => |it| {
            if (it.op != .bool_and) return;
            try check.gatherWhenTrue(it.lhs);
            try check.gatherWhenTrue(it.rhs);
        },
        else => {},
    }
}

fn factsOfIs(
    check: *Check,
    node: Node.Index,
) Allocator.Error!?struct { when_true: Fact, when_false: Fact } {
    const comp = check.comp;
    const view = check.tree.viewOf(node).is_expr;

    const name = check.narrowedName(view.operand) orelse return null;
    const found = if (check.activeNarrow(name)) |narrow| narrow.type else check.nameType(name);
    if (comp.pool.isUnion(found) == false) return null;

    const label = try check.resolveType(view.type_expr);
    if (label == .poison) return null;
    if (comp.pool.subsumes(found, label) == false) return null;
    const rest = try comp.pool.unionWithout(comp.gpa, found, label) orelse return null;

    const holds: Fact = .{ .name = name, .type = label, .node = node };
    const others: Fact = .{ .name = name, .type = rest, .node = node };
    if (view.negated) return .{ .when_true = others, .when_false = holds };
    return .{ .when_true = holds, .when_false = others };
}

fn applyFacts(check: *Check, range: Compilation.Range) Allocator.Error!void {
    var at = range.start;
    // by index, because the run belongs to the builder rather than to this call
    while (at < range.end()) : (at += 1) try check.applyFact(check.comp.facts.items[at]);
}

fn applyFact(check: *Check, fact: Fact) Allocator.Error!void {
    const active = check.activeNarrow(fact.name);
    const source: Ref = if (active) |narrow| narrow.ref else check.nameRef(fact.name);
    const found: Pool.Index = if (active) |narrow| narrow.type else check.nameType(fact.name);
    assert(check.comp.pool.subsumes(found, fact.type));

    // an arm naming every member proves what the name already is, which narrows nothing
    const narrowed: Ref = if (found == fact.type) source else switch (source.unwrap()) {
        .constant => |constant| .fromConstant(
            try check.comp.pool.narrowTo(check.comp.gpa, constant, fact.type),
        ),
        .inst => try check.emitOne(fact.node, .union_narrow, fact.type, source),
    };
    try check.comp.narrows.append(check.comp.gpa, .{
        .name = fact.name,
        .type = fact.type,
        .ref = narrowed,
    });
}

fn valueOfRef(ref: Ref, type_index: Pool.Index) Value {
    return switch (ref.unwrap()) {
        .constant => |constant| .{ .constant = constant },
        .inst => runtimeValue(ref, type_index),
    };
}

fn namedType(check: *Check, node: Node.Index, value: Value) Allocator.Error!?Pool.Index {
    switch (value) {
        .named_type => |type_index| return type_index,
        .named_generic => |decl_index| {
            const decl = check.comp.declAt(decl_index);
            try check.failGenericBare(node, check.comp.pool.stringText(decl.name));
            return .poison;
        },
        else => return null,
    }
}

fn checkIs(check: *Check, node: Node.Index, view: AST.View.Is) Allocator.Error!Value {
    const comp = check.comp;
    const operand = try check.checkExpr(view.operand, null);
    const label = try check.resolveType(view.type_expr);
    if (operand.stops()) return operand;
    if (label == .poison) return .poison;

    if (try check.namedType(view.operand, operand)) |named| {
        if (named == .poison) return .poison;
        if (check.unionBoundOfName(view.operand)) |bound| {
            if (try check.labelWithin(view.type_expr, label, bound) == false) return .poison;
        }
        return check.settledTruth(node, comp.pool.covers(label, named) != view.negated);
    }
    if (try check.valueOnly(view.operand, operand) == false) return .poison;

    const found = check.typeOf(operand);
    if (found == .poison) return .poison;
    if (comp.pool.isUnion(found) == false) {
        try check.failNotUnion(node, found, "'is' asks which member a union holds");
        return .poison;
    }
    if (try check.labelWithin(view.type_expr, label, found) == false) return .poison;

    if (operand == .constant) {
        const held = comp.pool.memberOfValue(operand.constant);
        return check.settledTruth(node, comp.pool.covers(label, held) != view.negated);
    }

    if (check.builder == null) return check.needRuntime(node, "an 'is' test");
    assert(operand == .runtime);
    const bools = try check.boolType(node);
    const tested = try check.emit(node, .union_is, bools, .{
        .probe = .{ .operand = refOf(operand), .member = label },
    });
    if (view.negated) return check.emitOneValue(node, .not, bools, tested);
    return runtimeValue(tested, bools);
}

fn settledTruth(check: *Check, node: Node.Index, holds: bool) Allocator.Error!Value {
    const bools = try check.boolType(node);
    return .{ .constant = try check.comp.pool.truth(check.comp.gpa, bools, holds) };
}

fn labelWithin(
    check: *Check,
    label_node: Node.Index,
    label: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!bool {
    const pool = &check.comp.pool;
    if (pool.subsumes(union_type, label)) return true;

    var stray = label;
    if (pool.isUnion(label)) {
        for (pool.unionMembers(label)) |member| {
            if (pool.unionHas(union_type, member)) continue;
            stray = member;
            break;
        }
    }
    try check.failNotMember(label_node, stray, union_type);
    return false;
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
    if (check.visibleDecl(name)) |decl_index| {
        const found = try check.declAsType(decl_index, node);
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

fn truthOf(check: *const Check, bools: Pool.Index, constant: Pool.Index) ?bool {
    if (bools == .poison) return null;
    const pool = &check.comp.pool;
    const found = pool.memberOfValue(constant);
    if (found == pool.unionMemberAt(bools, 0)) return true;
    if (found == pool.unionMemberAt(bools, 1)) return false;
    return null;
}

fn conditionTruth(check: *const Check, cond: Ref) ?bool {
    return switch (cond.unwrap()) {
        .inst => null,
        .constant => |value| if (value == .poison) null else check.comp.pool.holdsFirst(value),
    };
}

fn checkCondition(check: *Check, node: Node.Index) Allocator.Error!Ref {
    const value = try check.checkValue(node, null);
    const found = check.typeOf(value);
    if (found == .poison) return broken_ref;
    if (check.comp.pool.isUnion(found)) return refOf(value);
    try check.fail(node, .{
        .code = .not_a_union,
        .message = try check.comp.fmt("this condition is {s}, and a condition is a union", .{
            try check.comp.typeName(found),
        }),
        .label = "cannot answer",
        .help = "a condition asks whether a union holds its first member",
    });
    return broken_ref;
}

fn checkReturn(
    check: *Check,
    node: Node.Index,
    operand: Node.OptionalIndex,
) Allocator.Error!Value {
    const builder = check.body();
    if (builder.in_defer) {
        try check.failDeferLeaves(node, "no 'return' here");
        return .poison;
    }

    if (operand.unwrap()) |value_node| {
        if (builder.return_type == .void_type) {
            try check.fail(node, .{
                .code = .type_mismatch,
                .message = "this function returns nothing, and this 'return' carries a value",
                .label = "nothing expected",
                .help = "drop the value, or give the function a return type",
            });
            _ = try check.checkExpr(value_node, null);
            check.endBlock(.{ .ret = .none });
            return .diverged;
        }
        const value = try check.checkExpr(value_node, builder.return_type);
        const met = try check.coerce(value, builder.return_type, value_node);
        if (check.blockOpen() == false) return .diverged;
        try check.unwindScopesTo(0);
        check.endBlock(.{ .ret = refOf(met) });
        return .diverged;
    }

    if (builder.return_type != .void_type) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = try check.comp.fmt("'return' here must carry a {s}", .{
                try check.comp.typeName(builder.return_type),
            }),
            .label = "returns nothing",
        });
    }
    try check.unwindScopesTo(0);
    check.endBlock(.{ .ret = .none });
    return .diverged;
}

fn checkBreak(check: *Check, node: Node.Index, view: AST.View.Break) Allocator.Error!Value {
    const builder = check.body();

    const frame_index = try check.findLoop(node, view.label) orelse {
        if (view.value.unwrap()) |value_node| _ = try check.checkExpr(value_node, null);
        return .poison;
    };
    const frame = check.loopPtr(frame_index).*;

    if (view.value.unwrap()) |value_node| {
        if (frame.join.carries) {
            const value = try check.checkExpr(value_node, frame.join.armHint());
            if (check.blockOpen() == false) return .diverged;
            try check.loopPtr(frame_index).join.take(check, value, value_node);
        } else {
            try check.fail(node, .{
                .code = .type_mismatch,
                .message = "this 'break' carries a value, and its loop is not asked for one",
                .label = "nothing takes it",
                .help = "bind the loop, as in 'let v = loop { ... }', or drop the value",
            });
            _ = try check.checkExpr(value_node, null);
            if (check.blockOpen() == false) return .diverged;
        }
    } else if (frame.join.carries) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this loop stands where a value is needed, so 'break' must carry it",
            .label = "carries nothing",
        });
    }

    try check.unwindScopesTo(frame.scope_depth);
    if (builder.reachable) check.loopPtr(frame_index).broke_reachable = true;
    check.endBlock(.{ .jump = frame.exit });
    return .diverged;
}

fn checkContinue(check: *Check, node: Node.Index, label: ?Token.Index) Allocator.Error!Value {
    const frame_index = try check.findLoop(node, label) orelse return .poison;
    const frame = check.loopPtr(frame_index).*;
    try check.unwindScopesTo(frame.scope_depth);
    check.endBlock(.{ .jump = frame.header });
    return .diverged;
}

fn findLoop(check: *Check, node: Node.Index, label: ?Token.Index) Allocator.Error!?usize {
    const builder = check.body();
    const found: ?usize = found: {
        const token = label orelse {
            if (builder.loops.items.len == 0) break :found null;
            break :found builder.loops.items.len - 1;
        };
        const name = try check.comp.pool.string(check.comp.gpa, check.tree.tokenSlice(token));
        var index = builder.loops.items.len;
        while (index > 0) {
            index -= 1;
            if (builder.loops.items[index].label == name) break :found index;
        }
        break :found null;
    };

    const escapes_defer = if (found) |at| at < builder.defer_loops_floor else true;
    if (builder.in_defer and escapes_defer) {
        try check.failDeferLeaves(node, "not allowed here");
        return null;
    }
    if (found != null) return found;

    if (label) |token| {
        try check.fail(node, .{
            .code = .outside_loop,
            .message = try check.comp.fmt("no enclosing loop is labeled ':{s}'", .{
                check.tree.tokenSlice(token),
            }),
            .label = "no such loop",
        });
    } else {
        try check.fail(node, .{
            .code = .outside_loop,
            .message = "there is no loop here to leave",
            .label = "outside every loop",
        });
    }
    return null;
}

fn failDeferLeaves(check: *Check, node: Node.Index, label: []const u8) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .defer_cannot_leave,
        .message = "a 'defer' runs on the way out, so it cannot leave again",
        .label = label,
    });
}

fn expectNothing(check: *Check, node: Node.Index, value: Value) Allocator.Error!void {
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

pub fn checkExpr(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    if (check.builder == null) {
        if (runtimeOnly(check.tree.nodeTag(node))) |what| return check.needRuntime(node, what);
    }

    switch (check.tree.viewOf(node)) {
        .builtin => return Builtin.notAValue(check, node),
        .ident => return check.checkIdent(node),
        .number_literal => return check.checkNumber(node),
        .string_literal => return check.checkString(node),
        .multiline_string => |view| return check.checkMultilineString(view),
        .char_literal => return check.checkChar(node),
        .block => return check.checkBlockValue(node, hint),
        .if_expr => |view| return check.checkIf(node, view, hint),
        .loop_expr => |view| return check.checkLoop(node, view, hint),
        .match_expr => |view| return check.checkMatch(node, view, hint),
        .return_expr => |operand| return check.checkReturn(node, operand),
        .break_expr => |view| return check.checkBreak(node, view),
        .continue_expr => |label| return check.checkContinue(node, label),
        .binary => |view| return check.checkBinary(node, view, hint),
        .unary => |view| return check.checkUnary(node, view),
        .is_expr => |view| return check.checkIs(node, view),
        .or_bind => |view| return check.checkOrBind(node, view, hint),
        .field_access => |view| return check.checkFieldAccess(node, view),
        .deref => return check.checkDeref(node),
        .call => return check.checkCall(node, hint),
        .bracket => |view| return check.checkBracketExpr(node, view),
        .struct_literal => return check.checkStructLiteral(node, hint),
        .array_literal => return check.checkArrayLiteral(node, hint),
        // a bracket item may be written as a type, which is then not a value
        .array_type, .slice_type, .pointer_type, .union_type => {
            const resolved = try check.resolveType(node);
            return if (resolved == .poison) .poison else .{ .named_type = resolved };
        },
        .err => return .poison,
        // the parser keeps statements, declarations, and a stray range out of here
        .root, .import_decl, .struct_decl, .alias_decl, .unit_decl, .fn_decl => unreachable,
        .var_decl, .type_param, .param, .field, .assign, .defer_stmt => unreachable,
        .match_arm, .struct_field_init, .range_expr => unreachable,
    }
}

fn checkIdent(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const text = check.mainTokenText(node);

    if (Module.isDiscard(text)) {
        try check.failDiscard(node);
        return .poison;
    }

    if (check.findLocalIndex(text)) |index| {
        const local = check.localAt(index);
        if (local.kind == .var_slot) return check.emitOneValue(node, .load, local.type, local.ref);
        if (check.activeNarrow(.{ .local = index })) |narrow| {
            return valueOfRef(narrow.ref, narrow.type);
        }
        return valueOfRef(local.ref, local.type);
    }

    for (check.bindings) |binding| {
        if (comp.pool.sameText(binding.name, text)) return .{ .named_type = binding.type };
    }
    if (Pool.primitiveType(text)) |primitive| return .{ .named_type = primitive };
    if (check.visibleDecl(text)) |decl_index| {
        if (check.activeNarrow(.{ .decl = decl_index })) |narrow| {
            return valueOfRef(narrow.ref, narrow.type);
        }
        return check.declAsValue(decl_index, node);
    }

    try check.reportUndefined(node, text);
    return .poison;
}

fn declAsValue(check: *Check, decl_index: Decl.Index, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const decl = comp.declAt(decl_index);
    switch (decl.kind) {
        .let => {
            const result = try check.ensured(decl_index, node) orelse return .poison;
            return .{ .constant = @enumFromInt(result) };
        },
        .fn_decl => return .{ .named_fn = decl_index },
        .extern_fn => {
            if (try check.ensured(decl_index, node) == null) return .poison;
            return .{ .named_fn = decl_index };
        },
        .struct_decl => {
            if (comp.typeParamCount(decl_index) > 0) return .{ .named_generic = decl_index };
            const instance = try comp.instantiate(decl_index, &.{}, check.origin(node));
            return .{ .named_type = comp.instanceType(instance) };
        },
        .type_alias => {
            if (comp.typeParamCount(decl_index) > 0) return .{ .named_generic = decl_index };
            const result = try check.ensured(decl_index, node) orelse return .poison;
            return .{ .named_type = @enumFromInt(result) };
        },
        .unit_decl => {
            const unit_type = try comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
            return .{ .constant = try comp.pool.unitValue(comp.gpa, unit_type) };
        },
        .import => {
            if (try check.ensured(decl_index, node) == null) return .poison;
            return .{ .named_module = Module.importedModule(comp, decl_index) };
        },
    }
}

fn checkNumber(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    switch (try Literal.decodeNumber(comp.arena.allocator(), check.mainTokenText(node))) {
        .int => |value| return check.untypedInt(value),
        .float => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_float = .{ .type = .untyped_float_type, .value = value },
        }) },
        .refused => |refusal| return check.refuse(node, refusal),
    }
}

fn checkString(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var reading = Literal.bytesOf(check.mainTokenText(node));
    while (reading.next()) |piece| switch (piece) {
        .bytes => |run| try check.appendText(run),
        .refused => |refusal| return check.refuse(node, refusal),
    };
    return check.textValue(mark);
}

fn checkMultilineString(check: *Check, view: AST.View.MultilineString) Allocator.Error!Value {
    const comp = check.comp;
    assert(view.last.int() >= view.first.int());
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var line = view.first;
    while (true) : (line = line.after(1)) {
        assert(check.tree.tokenTag(line) == .string_line);
        if (line != view.first) try check.appendText("\n");
        try check.appendText(Literal.textLine(check.tree.tokenSlice(line)));
        if (line == view.last) break;
    }
    return check.textValue(mark);
}

/// Bytes, so a string never lands on a wider element than it spells.
fn appendText(check: *Check, run: []const u8) Allocator.Error!void {
    const comp = check.comp;
    const before = comp.pool.scratch.items.len;
    // interning touches the pool's items, never its scratch, so the reservation holds
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, run.len);
    for (run) |byte| {
        comp.pool.scratch.appendAssumeCapacity(try comp.pool.int(comp.gpa, .u8_type, byte));
    }
    assert(comp.pool.scratch.items.len == before + run.len);
}

fn textValue(check: *Check, mark: usize) Allocator.Error!Value {
    const comp = check.comp;
    assert(comp.pool.scratch.items.len >= mark);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = .untyped_aggregate_type,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

fn checkChar(check: *Check, node: Node.Index) Allocator.Error!Value {
    switch (Literal.decodeChar(check.mainTokenText(node))) {
        .codepoint => |value| return check.untypedInt(value),
        .refused => |refusal| return check.refuse(node, refusal),
    }
}

const Operation = struct {
    node: Node.Index,
    op: AST.BinaryOp,
    op_token: Token.Index,
    lhs: Value,
    lhs_node: Node.Index,
    rhs: Value,
    rhs_node: Node.Index,
};

fn checkBinary(
    check: *Check,
    node: Node.Index,
    view: AST.View.Binary,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    if (view.op == .bool_and) return check.checkShortCircuit(node, view);
    if (view.op == .bool_or) return check.checkOr(view, hint);

    const lhs = try check.checkValue(view.lhs, null);
    const rhs = try check.checkValue(view.rhs, null);
    if (lhs == .diverged or rhs == .diverged) return .diverged;
    if (lhs == .poison or rhs == .poison) return .poison;
    return check.combine(.{
        .node = node,
        .op = view.op,
        .op_token = view.op_token,
        .lhs = lhs,
        .lhs_node = view.lhs,
        .rhs = rhs,
        .rhs_node = view.rhs,
    });
}

fn combine(check: *Check, it: Operation) Allocator.Error!Value {
    const comp = check.comp;
    assert(it.op != .bool_and);
    assert(it.op != .bool_or);

    if (it.lhs == .constant and it.rhs == .constant) {
        const folded = try comp.pool.fold(comp.gpa, it.op, it.lhs.constant, it.rhs.constant);
        return check.settleFold(it.lhs_node, it.op_token, folded);
    }
    return check.emitBinary(it);
}

fn settleFold(
    check: *Check,
    node: Node.Index,
    op_token: Token.Index,
    folded: Pool.Fold,
) Allocator.Error!Value {
    const comp = check.comp;
    const report: Diagnostic.Report = switch (folded) {
        .value => |value| return .{ .constant = value },
        .truth => |holds| return check.settledTruth(node, holds),
        .overflow => .{
            .code = .overflow,
            .message = "this overflows the 128 bits constants fold in",
            .label = "too large",
        },
        .division_by_zero => .{
            .code = .division_by_zero,
            .message = "this divides by zero",
            .label = "the divisor is zero",
        },
        .bad_shift => |bad| .{
            .code = .bad_shift,
            .message = try comp.fmt("{s} shifts by 0 to {d}, and this shifts by {d}", .{
                try comp.typeName(bad.type),
                Pool.widthOf(bad.type) - 1,
                bad.count,
            }),
            .label = "not a shift count",
        },
        .does_not_fit => |missed| try check.doesNotFit(missed.value, missed.type, null),
        .mismatch => |pair| {
            try check.failMixedTypes(op_token, pair.left, pair.right, operand_help);
            return .poison;
        },
        .bad_operand => |operand_type| {
            try check.reportBadOperand(op_token, operand_type);
            return .poison;
        },
    };
    return check.refuseToken(op_token, report);
}

const operand_help = "nothing converts on its own, so give both sides one type";

const range_help = "the ends of a range take each other's type, and nothing converts on its own";

fn failMixedTypes(
    check: *Check,
    op_token: Token.Index,
    left: Pool.Index,
    right: Pool.Index,
    help: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.failToken(op_token, .{
        .code = .mixed_types,
        .message = try check.comp.fmt("'{s}' mixes {s} and {s}", .{
            check.tree.tokenSlice(op_token),
            try check.comp.typeName(left),
            try check.comp.typeName(right),
        }),
        .label = "two different types",
        .help = help,
    });
}

fn emitBinary(check: *Check, it: Operation) Allocator.Error!Value {
    const pool = &check.comp.pool;
    const lhs_type = check.typeOf(it.lhs);
    const rhs_type = check.typeOf(it.rhs);
    const left = Pool.sharedType(lhs_type, rhs_type) orelse {
        const union_side: ?Pool.Index = if (pool.isUnion(lhs_type))
            lhs_type
        else if (pool.isUnion(rhs_type))
            rhs_type
        else
            null;
        const equality = it.op == .equal or it.op == .not_equal;
        const help = if (union_side) |side|
            check.operandHelp(side, equality) orelse operand_help
        else
            operand_help;
        try check.failMixedTypes(it.op_token, lhs_type, rhs_type, help);
        return .poison;
    };

    const lhs = try check.coerce(it.lhs, left, it.lhs_node);
    const rhs = try check.coerce(it.rhs, left, it.rhs_node);
    if (lhs == .poison or rhs == .poison) return .poison;

    const how = loweringOf(it.op);
    const admissible = switch (how.takes) {
        .number => Pool.isNumeric(left),
        .whole => Pool.isInteger(left),
        .scalar => Pool.isNumeric(left) or check.comp.pool.keyOf(left) == .type_pointer,
    };
    if (admissible == false) {
        try check.reportBadOperand(it.op_token, left);
        return .poison;
    }

    const result_type = if (how.compares) try check.boolType(it.lhs_node) else left;
    return check.emitValue(it.node, .ofBinary(it.op), result_type, .{
        .bin = .{ .lhs = refOf(lhs), .rhs = refOf(rhs) },
    });
}

const Lowering = struct { takes: enum { number, whole, scalar } = .number, compares: bool = false };

fn loweringOf(op: AST.BinaryOp) Lowering {
    return switch (op) {
        .add, .sub, .mul, .div => .{},
        .mod, .bit_and, .bit_or, .bit_xor, .shift_left, .shift_right => .{ .takes = .whole },
        .equal, .not_equal => .{ .takes = .scalar, .compares = true },
        .less_than, .less_or_equal, .greater_than, .greater_or_equal => .{ .compares = true },
        // control flow, so `checkShortCircuit` and `checkOr` lower them as branches
        .bool_and, .bool_or => unreachable,
    };
}

/// `and` is control flow, so the lowering is a branch and a slot.
fn checkShortCircuit(
    check: *Check,
    node: Node.Index,
    view: AST.View.Binary,
) Allocator.Error!Value {
    assert(view.op == .bool_and);
    const comp = check.comp;
    const lhs = try check.checkExpr(view.lhs, null);
    const bools = try check.boolType(view.lhs);
    const lhs_met = try check.coerce(lhs, bools, view.lhs);
    if (lhs_met == .poison) {
        try check.checkAside(view.rhs);
        return .poison;
    }

    if (lhs_met == .constant) {
        const truth = check.truthOf(bools, lhs_met.constant) orelse return .poison;
        // the constant decided, so the dead side never runs and never gets checked
        if (truth == false) return lhs_met;
        const rhs = try check.checkExpr(view.rhs, null);
        return check.coerce(rhs, bools, view.rhs);
    }

    const slot = try check.emitSlot(node, .empty, bools);
    try check.emitStore(node, slot, refOf(lhs_met));

    const entry_reachable = check.body().reachable;
    const rhs_block = try check.newBlock();
    const join = try check.newBlock();
    check.endBlock(.{ .branch = .{
        .cond = refOf(lhs_met),
        .then_block = rhs_block,
        .else_block = join,
    } });

    check.startBlock(rhs_block);
    const facts_mark: u32 = @intCast(comp.facts.items.len);
    defer comp.facts.shrinkRetainingCapacity(facts_mark);

    const narrows_mark = comp.narrows.items.len;
    try check.applyFacts((try check.gatherFacts(view.lhs)).when_true);
    const rhs = try check.checkExpr(view.rhs, null);
    const rhs_met = try check.coerce(rhs, bools, view.rhs);
    if (rhs_met != .diverged) try check.emitStore(view.rhs, slot, refOf(rhs_met));
    comp.narrows.shrinkRetainingCapacity(narrows_mark);
    if (check.blockOpen()) check.endBlock(.{ .jump = join });

    check.startBlock(join);
    check.body().reachable = entry_reachable;
    return check.emitOneValue(node, .load, bools, slot);
}

fn checkOr(check: *Check, view: AST.View.Binary, hint: ?Pool.Index) Allocator.Error!Value {
    assert(view.op == .bool_or);
    const lhs = try check.checkValue(view.lhs, hint);
    if (lhs == .diverged) return .diverged;
    if (lhs == .poison) {
        try check.checkAside(view.rhs);
        return .poison;
    }
    const found = check.typeOf(lhs);
    if (check.comp.pool.isUnion(found) == false) {
        try check.failNotUnion(view.lhs, found, "'or' splits a union");
        try check.checkAside(view.rhs);
        return .poison;
    }
    if (check.builder == null) {
        assert(lhs == .constant);
        return check.checkOrFold(view.rhs, lhs.constant, found);
    }
    return check.checkOrSplit(view.lhs, refOf(lhs), found, view.rhs, .none);
}

/// Checks the right side of a broken `or` or `and` for its own reports.
fn checkAside(check: *Check, node: Node.Index) Allocator.Error!void {
    const builder = check.builder orelse {
        _ = try check.checkExpr(node, null);
        return;
    };
    const reachable = builder.reachable;
    _ = try check.checkExpr(node, null);
    try check.reopenDead();
    builder.reachable = reachable;
}

fn checkOrFold(
    check: *Check,
    rhs_node: Node.Index,
    lhs: Pool.Index,
    lhs_type: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(check.builder == null);
    assert(comp.pool.typeOfValue(lhs) == lhs_type);

    const first = comp.pool.firstMember(lhs_type);
    if (comp.pool.holdsFirst(lhs)) return .{ .constant = comp.pool.heldValue(lhs) };

    const rhs = try check.checkExpr(rhs_node, first);
    if (check.typeOf(rhs) == lhs_type) return rhs;
    return check.coerce(rhs, first, rhs_node);
}

fn checkOrBind(
    check: *Check,
    node: Node.Index,
    view: AST.View.OrBind,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const lhs = try check.checkValue(view.lhs, hint);
    if (lhs.stops()) return lhs;

    const found = check.typeOf(lhs);
    if (comp.pool.isUnion(found) == false) {
        try check.failNotUnion(node, found, "'or' with a handler splits a union");
        return .poison;
    }
    return check.checkOrSplit(view.lhs, refOf(lhs), found, view.block, view.binder.toOptional());
}

fn checkOrSplit(
    check: *Check,
    lhs_node: Node.Index,
    lhs: Ref,
    lhs_type: Pool.Index,
    rhs_node: Node.Index,
    binder: Node.OptionalIndex,
) Allocator.Error!Value {
    const comp = check.comp;
    const builder = check.body();
    const first = comp.pool.firstMember(lhs_type);
    const rest = try comp.pool.unionTail(comp.gpa, lhs_type);

    const slot = try check.emitSlot(lhs_node, .empty, lhs_type);
    try check.emitStore(lhs_node, slot, lhs);

    const entry_reachable = builder.reachable;
    const rhs_block = try check.newBlock();
    const join = try check.newBlock();
    check.endBlock(.{ .branch = .{
        .cond = lhs,
        .then_block = join,
        .else_block = rhs_block,
    } });

    check.startBlock(rhs_block);
    var widened = false;
    if (binder == .none and check.orPropagates(rhs_node)) {
        const rest_value = try check.emitOne(rhs_node, .union_narrow, rest, lhs);
        const met = try check.coerce(runtimeValue(rest_value, rest), builder.return_type, rhs_node);
        try check.unwindScopesTo(0);
        check.endBlock(.{ .ret = refOf(met) });
    } else {
        const facts_mark: u32 = @intCast(comp.facts.items.len);
        defer comp.facts.shrinkRetainingCapacity(facts_mark);

        const narrows_mark = comp.narrows.items.len;
        const facts = try check.gatherFacts(lhs_node);
        try check.applyFacts(facts.when_false);

        if (binder.unwrap()) |binder_node| {
            try check.pushScope();
            try check.bindRest(binder_node, lhs, rest);
        }
        const rhs = try check.checkExpr(rhs_node, first);
        if (binder != .none) check.popScope();

        widened = check.typeOf(rhs) == lhs_type;
        const met = if (widened) rhs else try check.coerce(rhs, first, rhs_node);
        if (met != .diverged) {
            const settled = if (widened or met == .poison)
                refOf(met)
            else
                try check.emit(rhs_node, .union_init, lhs_type, .{
                    .probe = .{ .operand = refOf(met), .member = first },
                });
            try check.emitStore(rhs_node, slot, settled);
        }
        comp.narrows.shrinkRetainingCapacity(narrows_mark);
        if (check.blockOpen()) check.endBlock(.{ .jump = join });
    }

    check.startBlock(join);
    builder.reachable = entry_reachable;
    const loaded = try check.emitOne(lhs_node, .load, lhs_type, slot);
    if (widened) return runtimeValue(loaded, lhs_type);
    return check.emitOneValue(lhs_node, .union_narrow, first, loaded);
}

fn orPropagates(check: *const Check, node: Node.Index) bool {
    if (check.tree.nodeTag(node) != .return_expr) return false;
    if (check.body().return_type == .void_type) return false;
    if (check.body().in_defer) return false;
    return check.tree.viewOf(node).return_expr == .none;
}

fn bindRest(
    check: *Check,
    binder_node: Node.Index,
    lhs: Ref,
    rest: Pool.Index,
) Allocator.Error!void {
    const text = check.mainTokenText(binder_node);
    if (Module.isDiscard(text)) return check.failDiscard(binder_node);
    const name = try check.comp.pool.string(check.comp.gpa, text);
    const narrowed = try check.emitOne(binder_node, .union_narrow, rest, lhs);
    try check.declareLocal(name, binder_node, .let, narrowed, rest);
}

fn checkUnary(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (view.op == .address_of) return check.checkAddressOf(node, view);

    const operand = try check.checkValue(view.operand, null);
    if (operand.stops()) return operand;
    const bools = if (view.op == .bool_not) try check.boolType(view.operand) else .poison;

    if (operand == .constant) {
        const folded: Pool.Fold = switch (view.op) {
            .negate => try comp.pool.foldNegate(comp.gpa, operand.constant),
            .bit_not => try comp.pool.foldBitNot(comp.gpa, operand.constant),
            .bool_not => not: {
                if (bools == .poison) break :not .{ .value = .poison };
                const truth = check.truthOf(bools, operand.constant) orelse
                    break :not .{ .bad_operand = check.typeOf(operand) };
                break :not .{ .truth = !truth };
            },
            .address_of => unreachable,
        };
        return check.settleFold(view.operand, view.op_token, folded);
    }

    const found = check.typeOf(operand);
    switch (view.op) {
        .negate => {
            if (Pool.isSignedNumber(found) == false) {
                return check.reportBadUnary(view, found, "needs a signed number");
            }
            return check.emitOneValue(node, .negate, found, refOf(operand));
        },
        .bit_not => {
            if (Pool.isInteger(found) == false) {
                return check.reportBadUnary(view, found, "needs an integer");
            }
            return check.emitOneValue(node, .bit_not, found, refOf(operand));
        },
        .bool_not => {
            const met = try check.coerce(operand, bools, view.operand);
            if (met == .poison) return .poison;
            return check.emitOneValue(node, .not, bools, refOf(met));
        },
        .address_of => unreachable,
    }
}

fn reportBadUnary(
    check: *Check,
    view: AST.View.Unary,
    found: Pool.Index,
    wants: []const u8,
) Allocator.Error!Value {
    return check.refuseToken(view.op_token, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'{s}' {s}, and this is {s}", .{
            check.tree.tokenSlice(view.op_token),
            wants,
            try check.comp.typeName(found),
        }),
        .label = "wrong operand type",
    });
}

fn checkAddressOf(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (check.builder == null) return check.needRuntime(node, "taking an address");

    const place = try check.checkPlace(view.operand) orelse return .poison;
    if (check.typeCanHold(place.type) == false) {
        return check.refuseToken(view.op_token, .{
            .code = .type_mismatch,
            .message = try comp.fmt("'&' needs a value with a type, and this is {s}", .{
                try comp.typeName(place.type),
            }),
            .label = "nothing to point at",
            .help = "give the value a type first, as in 'let n: i64 = 10'",
        });
    }
    const addressed = try check.placeAddress(place) orelse return .poison;
    return runtimeValue(addressed.ref, try check.pointerTo(addressed.type, addressed.mutable()));
}

fn checkFieldAccess(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
) Allocator.Error!Value {
    const comp = check.comp;
    const base = try check.checkExpr(view.lhs, null);
    switch (base) {
        .poison => return .poison,
        .diverged => return .diverged,
        .named_module => |target| {
            const member = try check.exported(target, node, view.name_token) orelse return .poison;
            return check.declAsValue(member, node);
        },
        .named_type, .named_generic => {
            return check.refuse(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("'{s}' is reached through a value or called, " ++
                    "and cannot be read", .{check.tree.tokenSlice(view.name_token)}),
                .label = "not a value",
            });
        },
        .named_fn => {
            try check.failFieldOnFunction(view.name_token);
            return .poison;
        },
        .constant, .runtime => return check.valueField(node, view, base),
    }
}

fn valueField(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
    base: Value,
) Allocator.Error!Value {
    const comp = check.comp;
    const reached = try check.reachField(check.typeOf(base), view.name_token) orelse return .poison;
    const row = switch (reached.member) {
        .field => |row| row,
        .method => unreachable,
        .length => |length| {
            const count = length orelse {
                const held = try check.viewValue(node, base, reached);
                return check.emitOneValue(node, .slice_len, .u64_type, held);
            };
            return .{ .constant = try comp.pool.int(comp.gpa, .u64_type, count) };
        },
        .address => |slice| {
            const held = try check.viewValue(node, base, reached);
            const result = try check.pointerTo(slice.child, slice.mutable);
            return check.emitOneValue(node, .slice_ptr, result, held);
        },
    };
    const row_type = comp.rowAt(row).type;

    if (reached.pointer == null and base == .constant and
        comp.pool.keyOf(base.constant) == .value_aggregate)
    {
        const rows = comp.instanceAt(comp.pool.structOf(reached.owner)).rows;
        return .{ .constant = comp.pool.aggregateAt(base.constant, row.int() - rows.start) };
    }

    const operand: IR.Inst.Data = .{ .field = .{ .base = refOf(base), .row = row } };
    if (reached.pointer) |it| {
        const field_pointer = try check.pointerTo(row_type, it.mutable);
        const place = try check.emit(node, .field_ptr, field_pointer, operand);
        return check.emitOneValue(node, .load, row_type, place);
    }
    return check.emitValue(node, .field_val, row_type, operand);
}

fn viewValue(check: *Check, node: Node.Index, base: Value, reached: Reach) Allocator.Error!Ref {
    if (reached.pointer == null) return refOf(base);
    return check.emitOne(node, .load, reached.owner, refOf(base));
}

const Member = union(enum) {
    field: Compilation.Row.Index,
    method: Decl.Index,
    length: ?u64,
    address: Pool.Key.Slice,

    const Kind = enum { field, method };
};

const length_name = "len";
const address_name = "ptr";

fn memberOf(check: *Check, owner: Pool.Index, name: []const u8) Allocator.Error!?Member {
    switch (check.comp.pool.keyOf(owner)) {
        .type_array => |array| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = array.len };
            return null;
        },
        .type_slice => |view| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = null };
            if (std.mem.eql(u8, name, address_name)) return .{ .address = view };
            return null;
        },
        .type_struct => |instance| return check.structMember(instance, name),
        else => return null,
    }
}

fn structMember(check: *Check, instance: Pool.Instance, name: []const u8) Allocator.Error!?Member {
    const comp = check.comp;
    try comp.ensureRows(instance);
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        if (comp.pool.sameText(comp.rowAt(.from(raw)).name, name)) return .{ .field = .from(raw) };
    }
    const members = comp.declAt(comp.instanceDecl(instance)).members();
    for (members.start..members.end()) |raw| {
        const member = comp.declAt(.from(raw));
        if (member.kind != .fn_decl) continue;
        if (comp.pool.sameText(member.name, name)) return .{ .method = .from(raw) };
    }
    return null;
}

const deref_help = "'.*' reads what a pointer points at, and a field is reached with '.name'";

pub fn pointerAt(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    what: []const u8,
    help: ?[]const u8,
) Allocator.Error!?Pool.Key.Pointer {
    switch (check.comp.pool.keyOf(found)) {
        .type_pointer => |it| return it,
        else => {},
    }
    try check.fail(node, .{
        .code = .type_mismatch,
        .message = try check.comp.fmt("'{s}' needs a pointer, and this is {s}", .{
            what,
            try check.comp.typeName(found),
        }),
        .label = "not a pointer",
        .help = help,
    });
    return null;
}

const Peeled = struct { pointer: ?Pool.Key.Pointer, owner: Pool.Index };

fn peelPointer(pool: *const Pool, from: Pool.Index) Peeled {
    switch (pool.keyOf(from)) {
        .type_pointer => |it| return .{ .pointer = it, .owner = it.child },
        else => return .{ .pointer = null, .owner = from },
    }
}

const Reach = struct { pointer: ?Pool.Key.Pointer, owner: Pool.Index, member: Member };

fn reachField(check: *Check, from: Pool.Index, name_token: Token.Index) Allocator.Error!?Reach {
    const peeled = peelPointer(&check.comp.pool, from);
    if (try check.memberOf(peeled.owner, check.tree.tokenSlice(name_token))) |member| {
        if (member == .field) {
            const owner = check.comp.pool.structOf(peeled.owner);
            if (try check.fieldIsVisible(owner, member.field, name_token) == false) return null;
        }
        if (member != .method) return .{
            .pointer = peeled.pointer,
            .owner = peeled.owner,
            .member = member,
        };
    }
    try check.reportNoMember(peeled.owner, name_token, .field);
    return null;
}

fn methodOf(check: *Check, owner: Pool.Index, name_token: Token.Index) Allocator.Error!?Decl.Index {
    if (try check.memberOf(owner, check.tree.tokenSlice(name_token))) |member| {
        if (member == .method) return member.method;
    }
    try check.reportNoMember(owner, name_token, .method);
    return null;
}

const narrow_help = "a 'let' narrows where a branch proves what it holds, so copy a 'var' " ++
    "or a field into one first";

fn reportNoMember(
    check: *Check,
    owner: Pool.Index,
    name_token: Token.Index,
    wanted: Member.Kind,
) Allocator.Error!void {
    const comp = check.comp;
    const name_text = check.tree.tokenSlice(name_token);
    if (owner == .poison) return;

    if (owner == .untyped_aggregate_type) {
        return check.failToken(name_token, .{
            .code = .no_such_member,
            .message = "this array has no type yet, so it has no members to reach",
            .label = "no type in sight",
            .help = not_landed_help,
        });
    }

    if (comp.pool.isUnion(owner)) {
        return check.failToken(name_token, .{
            .code = .not_narrowed,
            .message = try comp.fmt("{s} is a union, and reaching '{s}' means narrowing " ++
                "it first", .{
                try comp.typeName(owner), name_text,
            }),
            .label = "not narrowed",
            .help = narrow_help,
        });
    }

    if (try check.memberOf(owner, name_text)) |other| {
        const what: []const u8 = switch (other) {
            .method => try comp.fmt("a function, so call it with '.{s}(...)'", .{name_text}),
            .field => "a field, so it is read rather than called",
            .length => "a length, so it is read rather than called",
            .address => "the address a view holds, so it is read rather than called",
        };
        return check.failToken(name_token, .{
            .code = .no_such_member,
            .message = try comp.fmt("'{s}' is {s}", .{ name_text, what }),
            .label = try comp.fmt("not a {t}", .{wanted}),
        });
    }

    try check.failToken(name_token, .{
        .code = .no_such_member,
        .message = try comp.fmt("{s} has no {t} named '{s}'", .{
            try comp.typeName(owner), wanted, name_text,
        }),
        .label = try comp.fmt("no such {t}", .{wanted}),
        .help = try check.suggestMember(owner, name_text),
    });
}

fn failNotUnion(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    asks: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .not_a_union,
        .message = try check.comp.fmt("{s}, and this is {s}", .{
            asks,
            try check.comp.typeName(found),
        }),
        .label = "not a union",
    });
}

fn failNotMember(
    check: *Check,
    node: Node.Index,
    member: Pool.Index,
    union_type: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .not_a_member,
        .message = try check.comp.fmt("'{s}' is not a member of '{s}'", .{
            try check.comp.typeName(member),
            try check.comp.typeName(union_type),
        }),
        .label = "not a member",
    });
}

fn failFieldOnFunction(check: *Check, name_token: Token.Index) Allocator.Error!void {
    @branchHint(.cold);
    try check.failToken(name_token, .{
        .code = .no_such_member,
        .message = "a function has no fields, so call it first",
        .label = "'.' on a function",
    });
}

fn suggestMember(
    check: *Check,
    owner: Pool.Index,
    name_text: []const u8,
) Allocator.Error!?[]const u8 {
    const comp = check.comp;
    var closest: Closest = .{ .target = name_text };

    switch (comp.pool.keyOf(owner)) {
        .type_array => {
            if (std.mem.eql(u8, name_text, address_name)) {
                return "slice it to make a view of it, as in 'a[0..].ptr'";
            }
            closest.consider(length_name);
        },
        .type_slice => {
            closest.consider(length_name);
            closest.consider(address_name);
        },
        .type_struct => |instance| {
            for (comp.instanceRows(instance)) |row| {
                closest.consider(comp.pool.stringText(row.name));
            }
            const members = comp.declAt(comp.instanceDecl(instance)).members();
            for (members.slice(comp.decls.items)) |member| {
                if (member.kind == .fn_decl) closest.consider(comp.pool.stringText(member.name));
            }
        },
        else => return null,
    }
    return comp.didYouMean(closest);
}

fn memberIsVisible(check: *Check, member: Decl.Index, at: Token.Index) Allocator.Error!bool {
    const decl = check.comp.declAt(member);
    if (decl.module == check.module_index) return true;
    if (Module.declIsPub(check.comp, member)) return true;

    try check.failPrivate(at, decl.module, decl.node);
    return false;
}

/// A field without `pub` is reached only in its own file, the way a method is.
fn fieldIsVisible(
    check: *Check,
    owner: Pool.Instance,
    row: Compilation.Row.Index,
    at: Token.Index,
) Allocator.Error!bool {
    const comp = check.comp;
    const rows = comp.instanceAt(owner).rows;
    assert(row.int() >= rows.start);
    assert(row.int() < rows.end());

    const decl = comp.declAt(comp.instanceDecl(owner));
    if (decl.module == check.module_index) return true;
    const node = comp.rowAt(row).node;
    if (comp.treeOf(decl.module).viewOf(node).field.is_pub) return true;

    try check.failPrivate(at, decl.module, node);
    return false;
}

fn failPrivate(
    check: *Check,
    at: Token.Index,
    module: Module.Index,
    node: Node.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    assert(module != check.module_index);
    assert(check.tree.tokenTag(at) == .ident);
    try check.failToken(at, .{
        .code = .private,
        .message = try check.comp.fmt("'{s}' is private to its file", .{
            check.tree.tokenSlice(at),
        }),
        .label = "not public",
        .help = "mark it 'pub' to reach it from another file",
        .notes = try check.comp.noteOne(module, node, "declared here"),
    });
}

fn checkDeref(check: *Check, node: Node.Index) Allocator.Error!Value {
    const place = try check.checkPlace(node) orelse return .poison;
    return runtimeValue(try check.placeValue(place), place.type);
}

fn checkBracketExpr(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    if (check.baseIsNamespace(view.base) == false) return check.checkIndexExpr(node, view);

    const base = try check.checkExpr(view.base, null);
    switch (base) {
        .named_generic => {
            const resolved = try check.resolveBracketType(node);
            if (resolved == .poison) return .poison;
            return .{ .named_type = resolved };
        },
        .named_fn => {
            return check.refuse(node, .{
                .code = .not_a_function,
                .message = "a function with its type arguments is still not a value, so call it",
                .label = "missing the call",
            });
        },
        .diverged => return .diverged,
        .poison => return .poison,
        .constant, .runtime => return check.checkIndexExpr(node, view),
        else => {
            return check.refuse(node, .{
                .code = .generic_arguments,
                .message = "only a generic struct or function takes type arguments",
                .label = "arguments on the wrong thing",
            });
        },
    }
}

const Elements = struct {
    /// The bracket every check reaching through it reports at.
    node: Node.Index,
    base: Place,
    pointer: ?Pool.Key.Pointer,
    owner: Pool.Index,
    child: Pool.Index,
    len: ?u64,
    mutable: bool,
};

const Indexed = struct {
    elements: Elements,
    ref: Ref,
    /// The element it names, where the index is known before anything runs.
    at: ?u64,
};

fn checkIndexExpr(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    const comp = check.comp;
    if (check.rangeIn(view)) |range| return check.checkSlice(node, view, range);

    const indexed = try check.checkIndex(node, view) orelse return .poison;
    if (indexed.at) |at| {
        if (indexed.elements.pointer == null) {
            if (check.placeConstant(indexed.elements.base)) |aggregate| {
                return .{ .constant = comp.pool.aggregateAt(aggregate, at) };
            }
        }
    }

    // the fold above is the only way past here with no body to build in
    assert(check.builder != null);
    const place = try check.elementPlace(indexed.elements, indexed.ref) orelse return .poison;
    return runtimeValue(try check.placeValue(place), place.type);
}

/// The one bridge from storage to a view. Mutability follows the place the base names.
fn checkSlice(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
    range: AST.View.Range,
) Allocator.Error!Value {
    if (check.builder == null) return check.needRuntime(node, "making a view");

    const elements = try check.checkElements(node, view) orelse return .poison;
    const through = try check.elementsThrough(elements) orelse return .poison;
    const bounds = try check.checkRange(view.args[0], range, elements, through) orelse
        return .poison;

    if (refIsConstant(bounds.start) == false or refIsConstant(bounds.end) == false) {
        try check.emitCheck(elements.node, .order_check, bounds.start, bounds.end);
    }
    if (range.end != .none and settledAgainstBase(elements, bounds.end) == false) {
        const length = try check.baseLengthRef(elements, through);
        try check.emitCheck(elements.node, .order_check, bounds.end, length);
    }

    const made = try check.sliceOf(elements.child, through.mutable());
    const payload = try check.emitExtra(&.{
        @intFromEnum(through.ref),
        @intFromEnum(bounds.start),
        @intFromEnum(bounds.end),
    }, &.{});
    return check.emitValue(node, .slice_make, made, .{ .payload = payload });
}

const Bounds = struct { start: Ref, end: Ref };

fn checkRange(
    check: *Check,
    range_node: Node.Index,
    range: AST.View.Range,
    elements: Elements,
    through: Place,
) Allocator.Error!?Bounds {
    const start = try check.checkRangeEnd(range.start) orelse return null;
    const end_node = range.end.unwrap() orelse range_node;
    const end = if (range.end != .none)
        try check.checkRangeEnd(end_node) orelse return null
    else if (elements.len) |count|
        try check.untypedInt(count)
    else
        try check.emitOneValue(elements.node, .slice_len, .u64_type, through.ref);

    const ends = try check.settleEnds(
        range_node,
        .{ .value = start, .node = range.start },
        .{ .value = end, .node = end_node },
    ) orelse return null;

    if (check.countOf(ends.start)) |at| {
        if (at < 0) {
            try check.failBeforeFirst(range.start, "an end of a range", at);
            return null;
        }
    }
    if (check.countOf(ends.end)) |at| {
        if (at < 0) {
            try check.failBeforeFirst(end_node, "an end of a range", at);
            return null;
        }
    }
    if (try check.rangeRunsBackwards(range_node, ends.start, ends.end)) return null;
    if (check.countOf(ends.end)) |at| {
        if (elements.len) |count| {
            if (at > count) {
                try check.failPastLast(end_node, "this range ends at", at, elements, count);
                return null;
            }
        }
    }
    return .{ .start = refOf(ends.start), .end = refOf(ends.end) };
}

const End = struct { value: Value, node: Node.Index };

const Ends = struct { start: Value, end: Value, type: Pool.Index };

fn settleEnds(check: *Check, range_node: Node.Index, start: End, end: End) Allocator.Error!?Ends {
    const left = check.typeOf(start.value);
    const right = check.typeOf(end.value);
    if (Pool.isUntyped(left) == false and Pool.isUntyped(right) == false and left != right) {
        try check.failMixedTypes(check.tree.nodeMainToken(range_node), left, right, range_help);
        return null;
    }

    var settled = left;
    if (Pool.isUntyped(settled)) settled = right;
    if (Pool.isUntyped(settled)) settled = .u64_type;

    const first = try check.coerce(start.value, settled, start.node);
    const second = try check.coerce(end.value, settled, end.node);
    if (first == .poison or second == .poison) return null;
    return .{ .start = first, .end = second, .type = settled };
}

fn rangeRunsBackwards(
    check: *Check,
    range_node: Node.Index,
    start: Value,
    end: Value,
) Allocator.Error!bool {
    const low = check.countOf(start) orelse return false;
    const high = check.countOf(end) orelse return false;
    if (low <= high) return false;

    try check.failToken(check.tree.nodeMainToken(range_node), .{
        .code = .out_of_range,
        .message = try check.comp.fmt(
            "this range starts at {d} and ends at {d}, so it runs backwards",
            .{ low, high },
        ),
        .label = "the ends cross",
        .help = "a range runs from its start up to, but not including, its end",
    });
    return true;
}

fn countOf(check: *const Check, value: Value) ?i128 {
    if (value != .constant) return null;
    return switch (check.comp.pool.keyOf(value.constant)) {
        .value_int => |it| it.value,
        else => null,
    };
}

fn failBeforeFirst(
    check: *Check,
    node: Node.Index,
    what: []const u8,
    at: i128,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try check.comp.fmt("{s} counts from zero, and this one is {d}", .{ what, at }),
        .label = "before the first element",
    });
}

fn failPastLast(
    check: *Check,
    node: Node.Index,
    lead: []const u8,
    at: i128,
    elements: Elements,
    count: u64,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try check.comp.fmt("{s} {d}, and {s} holds {d} element{s}", .{
            lead, at, try check.comp.typeName(elements.owner), count, plural(count),
        }),
        .label = "past the last element",
    });
}

fn checkRangeEnd(check: *Check, node: Node.Index) Allocator.Error!?Value {
    const value = try check.checkValue(node, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found)) return value;
    try check.fail(node, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("an end of a range is a count, and this is {s}", .{
            try check.comp.typeName(found),
        }),
        .label = "not a count",
        .help = "any integer counts, and nothing else does",
    });
    return null;
}

fn rangeIn(check: *const Check, view: AST.View.Bracket) ?AST.View.Range {
    if (view.args.len != 1) return null;
    if (check.tree.nodeTag(view.args[0]) != .range_expr) return null;
    return check.tree.viewOf(view.args[0]).range_expr;
}

fn checkBracketArgs(check: *Check, view: AST.View.Bracket) Allocator.Error!void {
    for (view.args) |argument| {
        if (check.tree.nodeTag(argument) != .range_expr) {
            _ = try check.checkExpr(argument, null);
            continue;
        }
        const range = check.tree.viewOf(argument).range_expr;
        _ = try check.checkExpr(range.start, null);
        if (range.end.unwrap()) |end| _ = try check.checkExpr(end, null);
    }
}

fn checkIndex(check: *Check, node: Node.Index, view: AST.View.Bracket) Allocator.Error!?Indexed {
    const comp = check.comp;
    const elements = try check.checkElements(node, view) orelse return null;

    if (view.args.len != 1) {
        try check.checkBracketArgs(view);
        try check.fail(node, .{
            .code = .wrong_arity,
            .message = try comp.fmt("an index is one value, and this writes {d}", .{
                view.args.len,
            }),
            .label = "the wrong number of values",
            .help = "reach through one step at a time, as in 'grid[1][2]'",
        });
        return null;
    }

    const argument = view.args[0];
    const value = try check.checkValue(argument, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found) == false) {
        try check.fail(argument, .{
            .code = .bad_operand,
            .message = try comp.fmt("an index is a count, and this is {s}", .{
                try comp.typeName(found),
            }),
            .label = "not a count",
            .help = "any integer indexes, and nothing else does",
        });
        return null;
    }
    if (value != .constant) return .{ .elements = elements, .ref = refOf(value), .at = null };

    const written = comp.pool.keyOf(value.constant).value_int.value;
    if (written < 0) {
        try check.failBeforeFirst(argument, "an index", written);
        return null;
    }
    if (elements.len) |count| {
        if (written >= count) {
            try check.failPastLast(argument, "this index is", written, elements, count);
            return null;
        }
    }

    var ref = refOf(value);
    if (Pool.isUntyped(found)) {
        const met = try check.fitValue(value.constant, .u64_type, argument);
        // the value stands inside the length, which a u64 holds by construction
        assert(met == .constant);
        ref = refOf(met);
    }
    return .{ .elements = elements, .ref = ref, .at = @intCast(written) };
}

fn checkElements(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Elements {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .bracket);

    const base = try check.checkPlace(view.base) orelse return null;
    const peeled = peelPointer(&comp.pool, base.type);
    if (peeled.owner == .poison) return null;

    const key = comp.pool.keyOf(peeled.owner);
    const child: Pool.Index, const len: ?u64, const mutable: bool = switch (key) {
        .type_array => |it| .{ it.child, it.len, false },
        .type_slice => |it| .{ it.child, null, it.mutable },
        else => {
            try check.checkBracketArgs(view);
            try check.failNotIndexable(node, peeled.owner);
            return null;
        },
    };
    return .{
        .node = node,
        .base = base,
        .pointer = peeled.pointer,
        .owner = peeled.owner,
        .child = child,
        .len = len,
        .mutable = mutable,
    };
}

const not_landed_help = "give it a type, as in 'let a: [3]u32 = [1, 2, 3]', and " ++
    "everything it holds can be reached";

fn failNotIndexable(check: *Check, node: Node.Index, owner: Pool.Index) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;
    if (owner == .untyped_aggregate_type) {
        return check.fail(node, .{
            .code = .not_indexable,
            .message = "this array has no type yet, so it has no elements to reach",
            .label = "no type in sight",
            .help = not_landed_help,
        });
    }
    try check.fail(node, .{
        .code = .not_indexable,
        .message = try comp.fmt("{s} cannot be indexed", .{try comp.typeName(owner)}),
        .label = "not something to index",
        .help = "an index reaches an element, and an array is what holds elements",
    });
}

fn checkStructLiteral(
    check: *Check,
    node: Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const view = check.tree.viewOf(node).struct_literal;

    const wanted = try check.structLiteralType(node, view, hint) orelse return .poison;

    const instance = switch (comp.pool.keyOf(wanted)) {
        .type_struct => |instance| instance,
        else => {
            return check.refuse(view.type_expr.unwrap() orelse node, .{
                .code = .not_a_type,
                .message = try comp.fmt("{s} has no fields to give", .{
                    try comp.typeName(wanted),
                }),
                .label = "not a struct",
            });
        },
    };

    try comp.ensureRows(instance);
    const rows = comp.instanceAt(instance).rows;
    const buildable = try check.structIsBuildable(node, wanted, instance);

    const start: u32 = @intCast(comp.operands.items.len);
    defer comp.operands.shrinkRetainingCapacity(start);
    try comp.operands.appendNTimes(
        comp.gpa,
        .{ .value = .poison, .initializer = .none },
        rows.len,
    );

    var clean = true;
    for (view.fields) |init_node| {
        if (check.tree.nodeTag(init_node) != .struct_field_init) continue;
        const field_init = check.tree.viewOf(init_node).struct_field_init;

        const row: Compilation.Row.Index = row: {
            const name = check.tree.tokenSlice(field_init.name_token);
            if (try check.structMember(instance, name)) |member| {
                if (member == .field) break :row member.field;
            }
            try check.reportNoMember(wanted, field_init.name_token, .field);
            _ = try check.checkExpr(field_init.value, null);
            clean = false;
            continue;
        };
        const position: u32 = row.int() - rows.start;

        if (comp.operands.items[start + position].initializer.unwrap()) |first| {
            try check.failToken(field_init.name_token, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is given twice", .{
                    check.tree.tokenSlice(field_init.name_token),
                }),
                .label = "given again here",
                .notes = try check.noteHere(first, "first given here"),
            });
            clean = false;
            continue;
        }
        comp.operands.items[start + position].initializer = init_node.toOptional();

        const row_type = comp.rowAt(.from(rows.at(position))).type;
        const value = try check.checkExpr(field_init.value, row_type);
        const met = try check.coerce(value, row_type, field_init.value);
        if (met == .poison) clean = false;
        comp.operands.items[start + position].value = met;
    }
    // the values above are checked either way, so their own reports still land
    if (buildable == false) return .poison;

    var missing: []const u8 = "";
    for (0..rows.len) |position| {
        if (comp.operands.items[start + position].initializer != .none) continue;
        const name = comp.pool.stringText(comp.rowAt(.from(rows.at(@intCast(position)))).name);
        missing = try quotedList(comp, missing, name);
    }
    if (missing.len > 0) {
        return check.refuse(node, .{
            .code = .missing_field,
            .message = try comp.fmt("this literal leaves out {s}", .{missing}),
            .label = "incomplete",
            .help = "every field of the struct must be present, and there are no defaults",
        });
    }
    if (clean == false) return .poison;

    return check.settleAggregate(node, wanted, comp.operands.items[start..]);
}

fn structLiteralType(
    check: *Check,
    node: Node.Index,
    view: AST.View.StructLiteral,
    hint: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    if (view.type_expr.unwrap()) |written| {
        const resolved = try check.resolveType(written);
        return if (resolved == .poison) null else resolved;
    }

    const landing = hint orelse .void_type;
    if (landing == .poison) return null;
    if (landing != .void_type and check.comp.pool.isUnion(landing) == false) return landing;

    if (landing == .void_type) {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = "nothing here says which struct this builds",
            .label = "no type in sight",
            .help = "name it, as in 'Point.{ x: 1 }', or annotate what it feeds",
        });
    } else {
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = try check.comp.fmt(
                "this lands on '{s}', which lists several types, and nothing says which is built",
                .{try check.comp.typeName(landing)},
            ),
            .label = "which member?",
            .help = "name the struct, as in 'Point.{ x: 1 }'",
        });
    }
    return null;
}

/// A literal gives every field, so one it cannot reach keeps the whole literal in that file.
fn structIsBuildable(
    check: *Check,
    node: Node.Index,
    wanted: Pool.Index,
    instance: Pool.Instance,
) Allocator.Error!bool {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .struct_literal);
    assert(comp.pool.structOf(wanted) == instance);
    const decl = comp.declAt(comp.instanceDecl(instance));
    if (decl.module == check.module_index) return true;

    const tree = comp.treeOf(decl.module);
    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        const row = comp.rowAt(.from(raw));
        if (tree.viewOf(row.node).field.is_pub) continue;
        try check.fail(node, .{
            .code = .private,
            .message = try comp.fmt(
                "{s} keeps '{s}' private to its file, so only that file builds one",
                .{ try comp.typeName(wanted), comp.pool.stringText(row.name) },
            ),
            .label = "private fields",
            .help = "mark every field 'pub', or have that file build it through a function",
            .notes = try comp.noteOne(decl.module, row.node, "declared here"),
        });
        return false;
    }
    return true;
}

fn allConstant(operands: []const Operand) bool {
    for (operands) |operand| if (operand.value != .constant) return false;
    return true;
}

fn settleAggregate(
    check: *Check,
    node: Node.Index,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    if (allConstant(operands)) return check.internAggregate(type_index, operands);
    if (check.builder == null) {
        return check.refuse(node, .{
            .code = .not_constant,
            .message = "this must settle before anything runs, and part of this literal does not",
            .label = "not a constant",
        });
    }
    const payload = try check.emitExtra(&.{@intCast(operands.len)}, operands);
    return check.emitValue(node, .aggregate_init, type_index, .{ .payload = payload });
}

fn internAggregate(
    check: *Check,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    const comp = check.comp;
    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);
    try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, operands.len);
    for (operands) |operand| comp.pool.scratch.appendAssumeCapacity(operand.value.constant);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = type_index,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

fn checkArrayLiteral(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const comp = check.comp;
    const elements = check.tree.viewOf(node).array_literal;

    const landing: Pool.Index = if (hint) |found|
        aggregateLanding(&comp.pool, found, elements.len)
    else
        .void_type;
    const element_hint: ?Pool.Index = switch (comp.pool.keyOf(landing)) {
        .type_array => |it| it.child,
        .type_slice => |it| it.child,
        else => null,
    };

    const start = comp.operands.items.len;
    defer comp.operands.shrinkRetainingCapacity(start);
    try comp.operands.ensureUnusedCapacity(comp.gpa, elements.len);

    var clean = true;
    var diverged = false;
    for (elements) |element| {
        const value = try check.checkValue(element, element_hint);
        switch (value) {
            .diverged => diverged = true,
            .poison => clean = false,
            else => comp.operands.appendAssumeCapacity(.{ .value = value, .initializer = .none }),
        }
    }
    if (diverged) return .diverged;
    if (clean == false) return .poison;
    const operands = comp.operands.items[start..];

    const storage: Pool.Key.Array = switch (comp.pool.keyOf(landing)) {
        .type_array => |it| it,
        else => |key| {
            if (allConstant(operands)) {
                return check.internAggregate(.untyped_aggregate_type, operands);
            }
            return check.refuse(node, if (key == .type_slice) .{
                .code = .not_constant,
                .message = "a view needs bytes the program owns, and part of this " ++
                    "array is settled at run time",
                .label = "not a constant",
                .help = "bind it to storage first and slice that, as in " ++
                    "'var a: [4]u32 = ...' then 'a[0..]'",
            } else .{
                .code = .var_needs_type,
                .message = "nothing says what type this array is",
                .label = "no type in sight",
                .help = "annotate what it feeds, as in 'let a: [2]u32 = ...'",
            });
        },
    };

    if (storage.len != elements.len) {
        return check.refuse(node, .{
            .code = .does_not_fit,
            .message = try comp.fmt("this literal has {d} element{s}, and {s} holds {d}", .{
                elements.len,
                plural(@intCast(elements.len)),
                try comp.typeName(landing),
                storage.len,
            }),
            .label = "the wrong number of elements",
        });
    }

    for (elements, operands) |element, *operand| {
        operand.value = try check.coerce(operand.value, storage.child, element);
        if (operand.value == .poison) clean = false;
    }
    if (clean == false) return .poison;
    return check.settleAggregate(node, landing, operands);
}

fn aggregateLanding(pool: *const Pool, found: Pool.Index, count: usize) Pool.Index {
    if (pool.isUnion(found) == false) return found;
    for (pool.unionMembers(found)) |member| {
        switch (pool.keyOf(member)) {
            .type_array => |array| if (array.len == count) return member,
            .type_slice => return member,
            else => {},
        }
    }
    return found;
}

fn emitExtra(
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

/// Reads the substituted signature, never a body.
fn checkCall(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const view = check.tree.viewOf(node).call;
    if (view.args.len > call_args_max) {
        return check.refuse(node, .{
            .code = .wrong_arity,
            .message = try check.comp.fmt("a call takes at most {d} arguments", .{call_args_max}),
        });
    }

    var explicit: ?[]const Node.Index = null;
    var callee_node = view.callee;
    if (check.tree.nodeTag(callee_node) == .bracket) {
        const bracket = check.tree.viewOf(callee_node).bracket;
        explicit = bracket.args;
        callee_node = bracket.base;
    }
    const callee = try check.resolveCallee(callee_node) orelse return check.abandonCall(view.args);
    if (explicit) |written| {
        if (written.len > type_params_max) {
            try check.fail(view.callee, .{
                .code = .generic_arguments,
                .message = try check.comp.fmt(
                    "a call takes at most {d} type arguments",
                    .{type_params_max},
                ),
            });
            return check.abandonCall(view.args);
        }
    }

    if (callee == .builtin) {
        const which = callee.builtin;
        if (check.builder == null and which.needsBody()) {
            const name = try check.comp.fmt("'@{s}'", .{@tagName(which)});
            return check.needRuntime(node, name);
        }
        return which.call(check, node, explicit orelse &.{}, view.args, hint);
    }
    return check.checkCallResolved(node, callee, explicit, view.args, hint);
}

fn abandonCall(check: *Check, args: []const Node.Index) Allocator.Error!Value {
    for (args) |argument| _ = try check.checkExpr(argument, null);
    return .poison;
}

const Callee = union(enum) {
    builtin: Builtin,
    direct: Decl.Index,
    static: struct { decl: Decl.Index, owner: Pool.Instance },
    method: struct { receiver: Node.Index, name_token: Token.Index },
};

fn resolveCallee(check: *Check, node: Node.Index) Allocator.Error!?Callee {
    switch (check.tree.viewOf(node)) {
        .builtin => |name_token| {
            const which = try Builtin.resolve(check, name_token) orelse return null;
            return .{ .builtin = which };
        },
        .field_access => |access| return check.resolveCalleeMember(node, access),
        else => {
            const value = try check.checkExpr(node, null);
            return check.calleeOfValue(node, value);
        },
    }
}

/// Pure name chains reach modules and types. Anything else is a receiver, unevaluated.
fn resolveCalleeMember(
    check: *Check,
    callee_node: Node.Index,
    access: AST.View.FieldAccess,
) Allocator.Error!?Callee {
    const comp = check.comp;

    if (check.baseIsNamespace(access.lhs)) {
        const base = try check.checkExpr(access.lhs, null);
        switch (base) {
            .poison, .diverged => return null,
            .named_module => |target| {
                const member = try check.exported(target, callee_node, access.name_token) orelse
                    return null;
                const value = try check.declAsValue(member, callee_node);
                return check.calleeOfValue(callee_node, value);
            },
            .named_type => |type_index| {
                if (comp.pool.keyOf(type_index) != .type_struct) {
                    try check.failToken(access.name_token, .{
                        .code = .no_such_member,
                        .message = try comp.fmt("{s} has no functions to call", .{
                            try comp.typeName(type_index),
                        }),
                        .label = "nothing here",
                    });
                    return null;
                }
                const member = try check.methodOf(type_index, access.name_token) orelse return null;
                if (try check.memberIsVisible(member, access.name_token) == false) return null;
                return .{ .static = .{ .decl = member, .owner = comp.pool.structOf(type_index) } };
            },
            .named_generic => {
                try check.fail(access.lhs, .{
                    .code = .generic_arguments,
                    .message = "this is generic, so write its arguments before reaching in",
                    .label = "missing type arguments",
                });
                return null;
            },
            .named_fn => {
                try check.failFieldOnFunction(access.name_token);
                return null;
            },
            .constant, .runtime => {},
        }
    }
    return .{ .method = .{ .receiver = access.lhs, .name_token = access.name_token } };
}

fn baseIsNamespace(check: *const Check, node: Node.Index) bool {
    var current = node;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        switch (check.tree.nodeTag(current)) {
            .ident => return check.findLocalIndex(check.mainTokenText(current)) == null,
            .field_access => current = check.tree.viewOf(current).field_access.lhs,
            .bracket => current = check.tree.viewOf(current).bracket.base,
            else => return false,
        }
    }
    return false;
}

fn calleeOfValue(check: *Check, node: Node.Index, value: Value) Allocator.Error!?Callee {
    const comp = check.comp;
    switch (value) {
        .named_fn => |decl_index| return .{ .direct = decl_index },
        .poison, .diverged => return null,
        .constant, .runtime => {
            try check.fail(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("this is {s}, not a function", .{
                    try comp.typeName(check.typeOf(value)),
                }),
                .label = "cannot be called",
            });
            return null;
        },
        .named_type, .named_generic => {
            try check.fail(node, .{
                .code = .not_a_function,
                .message = "a type is not callable, and there are no conversions to call",
                .label = "a type",
            });
            return null;
        },
        .named_module => {
            try check.fail(node, .{
                .code = .not_a_function,
                .message = "a module is not callable, so name a function inside it",
                .label = "a module",
            });
            return null;
        },
    }
}

const Receiver = struct { place: Place, node: Node.Index };

fn checkCallResolved(
    check: *Check,
    node: Node.Index,
    callee: Callee,
    explicit: ?[]const Node.Index,
    args: []const Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;

    var receiver: ?Receiver = null;
    var owner_args: []const Pool.Index = &.{};
    const decl_index: Decl.Index = switch (callee) {
        .builtin => unreachable,
        .direct => |direct| direct,
        .static => |static| static: {
            owner_args = comp.instanceArgs(static.owner);
            break :static static.decl;
        },
        .method => |method| method: {
            const place = try check.checkPlace(method.receiver) orelse return .poison;
            if (place.type == .poison) return .poison;
            receiver = .{ .place = place, .node = method.receiver };

            const type_struct = peelPointer(&comp.pool, place.type).owner;
            const member = try check.methodOf(type_struct, method.name_token) orelse
                return .poison;
            if (try check.memberIsVisible(member, method.name_token) == false) return .poison;

            owner_args = comp.instanceArgs(comp.pool.structOf(type_struct));
            break :method member;
        },
    };

    const decl = comp.declAt(decl_index);
    const fn_name = comp.pool.stringText(decl.name);
    const own_count = comp.typeParamCount(decl_index);

    var full_args: [bindings_max]Pool.Index = undefined;
    assert(owner_args.len <= type_params_max);
    assert(own_count <= type_params_max);
    assert(owner_args.len + own_count <= full_args.len);
    @memcpy(full_args[0..owner_args.len], owner_args);
    const owner_count: u32 = @intCast(owner_args.len);

    const mark: u32 = @intCast(comp.operands.items.len);
    defer comp.operands.shrinkRetainingCapacity(mark);

    var inferred = false;
    if (explicit) |written| {
        if (written.len != own_count) {
            const declared = try comp.noteOne(decl.module, decl.node, "declared here");
            try check.failArity(node, fn_name, .type, own_count, written.len, declared);
            return .poison;
        }
        for (written, 0..) |argument, position| {
            const resolved = try check.resolveWrittenType(argument);
            if (resolved == .poison) return .poison;
            full_args[owner_count + position] = resolved;
        }
    } else if (own_count > 0) {
        const solved = try check.inferTypeArguments(
            node,
            decl_index,
            receiver != null,
            args,
            hint,
            full_args[owner_count..][0..own_count],
        );
        if (solved == false) return .poison;
        inferred = true;
    }
    const start: u32 = if (inferred) mark + @as(u32, @intCast(args.len)) else mark;

    if (try check.boundsHold(decl_index, full_args[owner_count..][0..own_count], node) == false) {
        return .poison;
    }

    const instance = try comp.instantiate(
        decl_index,
        full_args[0 .. owner_count + own_count],
        check.origin(node),
    );
    try comp.ensure(.of(.signature, instance), check.origin(node));
    if (comp.instanceAt(instance).rows_state != .done) return .poison;
    const return_type = comp.instanceType(instance);

    const rows = comp.instanceAt(instance).rows;
    var receiver_count: u32 = 0;
    if (receiver) |it| {
        if (rows.len == 0) {
            return check.refuse(node, .{
                .code = .wrong_arity,
                .message = try comp.fmt("'{s}' takes no parameters, so it has no receiver", .{
                    fn_name,
                }),
                .label = "not a method",
                .help = "call it through the type instead",
                .notes = try comp.noteOne(decl.module, decl.node, "declared here"),
            });
        }
        const self_type = comp.rowAt(.from(rows.at(0))).type;
        const adapted = try check.adaptReceiver(it.node, it.place, self_type, fn_name) orelse
            return .poison;
        try comp.operands.append(comp.gpa, .{
            .value = runtimeValue(adapted, self_type),
            .initializer = .none,
        });
        receiver_count = 1;
    }

    const expected = rows.len - receiver_count;
    if (args.len != expected) {
        const declared = try comp.noteOne(decl.module, decl.node, "declared here");
        try check.failArity(node, fn_name, .value, expected, args.len, declared);
        if (inferred == false) {
            for (args) |argument| _ = try check.checkExpr(argument, null);
        }
        return .poison;
    }

    // an argument is never checked twice, because checking emits
    var clean = true;
    for (args, 0..) |argument, position| {
        const at = receiver_count + @as(u32, @intCast(position));
        const row_type = comp.rowAt(.from(rows.at(at))).type;
        const value = if (inferred)
            comp.operands.items[mark + position].value
        else
            try check.checkExpr(argument, row_type);
        const met = try check.coerce(value, row_type, argument);
        if (met == .poison) clean = false;
        try comp.operands.append(comp.gpa, .{ .value = met, .initializer = .none });
    }
    if (clean == false) return .poison;
    assert(comp.operands.items.len == start + receiver_count + args.len);

    const operands = comp.operands.items[start..];
    if (check.builder == null) return Comptime.call(check, node, instance, operands);

    const payload = try check.emitExtra(&.{ instance.int(), @intCast(operands.len) }, operands);
    return check.emitValue(node, .call, return_type, .{ .payload = payload });
}

pub fn plural(count: u64) []const u8 {
    return if (count == 1) "" else "s";
}

fn quotedList(
    comp: *Compilation,
    so_far: []const u8,
    name: []const u8,
) Allocator.Error![]const u8 {
    if (so_far.len == 0) return comp.fmt("'{s}'", .{name});
    return comp.fmt("{s}, '{s}'", .{ so_far, name });
}

/// Omitted bracket arguments, pinned by parameter types, then by the call-site hint.
fn inferTypeArguments(
    check: *Check,
    node: Node.Index,
    decl_index: Decl.Index,
    has_receiver: bool,
    args: []const Node.Index,
    hint: ?Pool.Index,
    out: []Pool.Index,
) Allocator.Error!bool {
    const comp = check.comp;
    const decl = comp.declAt(decl_index);
    const owner_tree = comp.treeOf(decl.module);
    const fn_view = owner_tree.viewOf(decl.node).fn_decl;
    const fn_name = comp.pool.stringText(decl.name);

    const early: u32 = @intCast(comp.operands.items.len);
    for (args) |argument| {
        const value = try check.checkExpr(argument, null);
        try comp.operands.append(comp.gpa, .{ .value = value, .initializer = .none });
    }

    var callee = context(comp, decl_index);

    const receiver_rows: u32 = if (has_receiver) 1 else 0;
    for (fn_view.type_params, 0..) |type_param, param_position| {
        const wanted = owner_tree.tokenSlice(owner_tree.nodeMainToken(type_param));
        const bound = try callee.boundOf(decl_index, type_param);

        const pinned = check.pinnedType(
            owner_tree,
            fn_view,
            wanted,
            receiver_rows,
            @intCast(args.len),
            early,
        );

        const literal: ?Pool.Index = literal: {
            if (pinned != .unread) break :literal null;
            if (pinned.unread.argument >= args.len) break :literal null;
            const value = comp.operands.items[early + pinned.unread.argument].value;
            if (value != .constant) break :literal null;
            break :literal if (Pool.isUntyped(check.typeOf(value))) value.constant else null;
        };
        var from_hint = hintFor(&comp.pool, owner_tree, fn_view, wanted, hint);
        if (from_hint) |hinted| {
            if (bound) |limit| from_hint = try admittedBy(comp, limit, hinted, literal);
        }

        const pin = switch (pinned) {
            .type => |found| {
                out[param_position] = found;
                continue;
            },
            .poison => return false,
            .unread => |named| named,
            .none => {
                if (from_hint) |pinned_type| {
                    out[param_position] = pinned_type;
                    continue;
                }
                try check.fail(node, .{
                    .code = .inference_failed,
                    .message = try comp.fmt(
                        "no value parameter of '{s}' pins '{s}', so it must be written",
                        .{ fn_name, wanted },
                    ),
                    .label = "cannot be inferred",
                    .help = try comp.fmt("write the call '{s}[...](...)'", .{fn_name}),
                });
                return false;
            },
        };

        if (from_hint) |pinned_type| {
            out[param_position] = pinned_type;
            continue;
        }

        if (pin.argument >= args.len) {
            try check.fail(node, .{
                .code = .inference_failed,
                .message = try comp.fmt("'{s}' would be pinned by an argument this call lacks", .{
                    wanted,
                }),
                .label = "too few arguments to infer from",
            });
            return false;
        }

        const value = comp.operands.items[early + pin.argument].value;
        const found = check.typeOf(value);
        if (Pool.isUntyped(found)) {
            if (bound) |limit| if (wrapperOf(owner_tree, pin.written) == null) {
                const met = try check.fitValue(value.constant, limit, args[pin.argument]);
                if (met != .constant) return false;
                out[param_position] = comp.pool.memberOfValue(met.constant);
                continue;
            };
            try check.fail(args[pin.argument], .{
                .code = .inference_failed,
                .message = "a constant that has not landed has no type to read",
                .label = try comp.fmt("what type is '{s}'?", .{wanted}),
                .help = try comp.fmt(
                    "write the type argument, '{s}[i64](...)', type the value first, " ++
                        "or annotate what the call feeds",
                    .{fn_name},
                ),
            });
            return false;
        }

        const span = owner_tree.nodeSpan(pin.written);
        try check.fail(args[pin.argument], .{
            .code = .inference_failed,
            .message = try comp.fmt("'{s}' takes '{s}' here, so {s} cannot pin '{s}'", .{
                fn_name,
                owner_tree.source[span.start..span.end],
                try comp.typeName(found),
                wanted,
            }),
            .label = "the wrong shape to read a type from",
            .help = try comp.fmt("pass what the parameter is written as, or write " ++
                "the type argument '{s}[...](...)'", .{fn_name}),
        });
        return false;
    }
    return true;
}

const Pinned = union(enum) {
    type: Pool.Index,
    /// No argument had a type to read, and this is the parameter a report names.
    unread: Pin,
    /// An argument was already refused.
    poison,
    /// No value parameter is written in the type parameter.
    none,
};

fn pinnedType(
    check: *Check,
    tree: *const AST,
    fn_view: AST.View.FnDecl,
    wanted: []const u8,
    receiver_rows: u32,
    args_len: u32,
    early: u32,
) Pinned {
    const comp = check.comp;
    var first: ?Pin = null;
    for (fn_view.params, 0..) |param_node, position| {
        if (position < receiver_rows) continue;
        if (tree.nodeTag(param_node) != .param) continue;
        const written = tree.viewOf(param_node).param.type_expr;
        if (namesTypeParam(tree, written, wanted) == false) continue;

        const pin: Pin = .{ .argument = @intCast(position - receiver_rows), .written = written };
        if (first == null) first = pin;
        if (pin.argument >= args_len) continue;

        const value = comp.operands.items[early + pin.argument].value;
        const found = check.typeOf(value);
        if (found == .poison) return .poison;
        if (Pool.isUntyped(found)) {
            const inside = elementTypeInside(&comp.pool, tree, written, value) orelse continue;
            return .{ .type = inside };
        }
        const peeled = peelToTypeParam(&comp.pool, tree, written, found) orelse continue;
        return .{ .type = peeled };
    }
    return if (first) |named| .{ .unread = named } else .none;
}

fn elementTypeInside(
    pool: *const Pool,
    tree: *const AST,
    written: Node.Index,
    value: Value,
) ?Pool.Index {
    if (value != .constant) return null;
    var node = written;
    var current = value.constant;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        const found = pool.typeOfValue(current);
        const it = wrapperOf(tree, node) orelse {
            return if (Pool.isUntyped(found)) null else found;
        };
        if (found != .untyped_aggregate_type) return null;
        if (it.kind == .pointer) return null;
        if (pool.aggregateLen(current) == 0) return null;
        node = it.child;
        current = pool.aggregateAt(current, 0);
    }
    return null;
}

fn hintFor(
    pool: *const Pool,
    tree: *const AST,
    fn_view: AST.View.FnDecl,
    wanted: []const u8,
    hint: ?Pool.Index,
) ?Pool.Index {
    const usable = hint orelse return null;
    if (usable == .void_type) return null;
    if (usable == .poison) return null;

    const returned = fn_view.return_type.unwrap() orelse return null;
    if (namesTypeParam(tree, returned, wanted) == false) return null;
    return peelToTypeParam(pool, tree, returned, usable);
}

/// A value parameter that names the type parameter, and the argument that feeds it.
const Pin = struct { argument: u32, written: Node.Index };

/// One set, so a new wrapper joins both walks at once.
const Wrapper = enum { pointer, slice, array };

fn wrapperOf(tree: *const AST, node: Node.Index) ?struct { kind: Wrapper, child: Node.Index } {
    return switch (tree.nodeTag(node)) {
        .pointer_type => .{ .kind = .pointer, .child = tree.viewOf(node).pointer_type.child },
        .slice_type => .{ .kind = .slice, .child = tree.viewOf(node).slice_type.child },
        .array_type => .{ .kind = .array, .child = tree.viewOf(node).array_type.child },
        else => null,
    };
}

fn unwrap(pool: *const Pool, kind: Wrapper, type_index: Pool.Index) ?Pool.Index {
    const key = pool.keyOf(type_index);
    return switch (kind) {
        .pointer => if (key == .type_pointer) key.type_pointer.child else null,
        .slice => if (key == .type_slice) key.type_slice.child else null,
        .array => if (key == .type_array) key.type_array.child else null,
    };
}

fn namesTypeParam(tree: *const AST, written: Node.Index, wanted: []const u8) bool {
    var node = written;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        if (wrapperOf(tree, node)) |it| {
            node = it.child;
            continue;
        }
        if (tree.nodeTag(node) != .ident) return false;
        return std.mem.eql(u8, tree.tokenSlice(tree.nodeMainToken(node)), wanted);
    }
    return false;
}

fn peelToTypeParam(
    pool: *const Pool,
    tree: *const AST,
    written: Node.Index,
    found: Pool.Index,
) ?Pool.Index {
    var node = written;
    var current = found;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        const it = wrapperOf(tree, node) orelse return current;
        node = it.child;
        current = unwrap(pool, it.kind, current) orelse return null;
    }
    return null;
}

fn adaptReceiver(
    check: *Check,
    receiver_node: Node.Index,
    place: Place,
    self_type: Pool.Index,
    fn_name: []const u8,
) Allocator.Error!?Ref {
    const comp = check.comp;
    assert(place.type != .poison);
    if (place.type == self_type) return try check.placeValue(place);

    const place_key = comp.pool.keyOf(place.type);
    switch (comp.pool.keyOf(self_type)) {
        .type_pointer => |wanted| {
            if (place_key == .type_pointer and place_key.type_pointer.child == wanted.child) {
                if (wanted.mutable and place_key.type_pointer.mutable == false) {
                    try check.fail(receiver_node, .{
                        .code = .write_through_pointer,
                        .message = try comp.fmt(
                            "'{s}' writes through its receiver, and this is a '{s}'",
                            .{ fn_name, try comp.typeName(place.type) },
                        ),
                        .label = "read-only pointer",
                        .help = try comp.fmt("it needs '{s}'", .{try comp.typeName(self_type)}),
                    });
                    return null;
                }
                return try check.placeValue(place);
            }
            if (place.type == wanted.child) {
                if (wanted.mutable) {
                    if (place.immutable) |why| {
                        try check.reportReceiverImmutable(receiver_node, place, why, fn_name);
                        return null;
                    }
                }
                const addressed = try check.placeAddress(place) orelse return null;
                return addressed.ref;
            }
        },
        else => if (place_key == .type_pointer and place_key.type_pointer.child == self_type) {
            const pointer = try check.placeValue(place);
            return try check.emitOne(receiver_node, .load, self_type, pointer);
        },
    }
    try check.fail(receiver_node, .{
        .code = .type_mismatch,
        .message = try comp.fmt("the first parameter of '{s}' is {s}, so {s} " ++
            "cannot be its receiver", .{
            fn_name,
            try comp.typeName(self_type),
            try comp.typeName(place.type),
        }),
        .label = "receiver and parameter disagree",
    });
    return null;
}

fn reportReceiverImmutable(
    check: *Check,
    node: Node.Index,
    place: Place,
    why: Place.Reason,
    fn_name: []const u8,
) Allocator.Error!void {
    const what: []const u8 = switch (why) {
        .let_bound => "was bound with 'let'",
        .param_bound => "is a parameter, a copy that dies with the call",
        .read_only => |crossed| try check.comp.fmt("sits behind a '{s}', which is read-only", .{
            try check.comp.typeName(try check.crossedType(crossed, false)),
        }),
        .temporary => "is a temporary that no one else can see",
    };
    try check.fail(node, .{
        .code = .not_assignable,
        .message = try check.comp.fmt("'{s}' writes through its receiver, and '{s}' {s}", .{
            fn_name, place.root_name, what,
        }),
        .label = "immutable receiver",
        .help = "bind it with 'var' to let a method change it",
    });
}

const Place = struct {
    kind: Kind,
    /// The address for `.address`, the value itself for `.value`.
    ref: Ref,
    /// The type at this point of the chain, the pointee for `.address`.
    type: Pool.Index,
    node: Node.Index,
    /// Why the place cannot be written, null where it can.
    immutable: ?Reason,
    root_name: []const u8,
    root_node: Node.Index,

    const Kind = enum { address, value };
    const Reason = union(enum) {
        let_bound,
        param_bound,
        /// The read-only pointer or view the chain crossed, for the message.
        read_only: Crossed,
        temporary,
    };

    const Crossed = struct { form: enum { pointer, slice }, child: Pool.Index };

    fn mutable(place: Place) bool {
        return place.immutable == null;
    }

    fn crossing(place: Place, writable: bool, crossed: Crossed) Place {
        var beyond = place;
        beyond.immutable = if (writable) null else .{ .read_only = crossed };
        return beyond;
    }

    fn reaching(place: Place, node: Node.Index, ref: Ref, type_index: Pool.Index) Place {
        var reached = place;
        reached.kind = .address;
        reached.ref = ref;
        reached.type = type_index;
        reached.node = node;
        return reached;
    }
};

/// The pointer or view a chain crossed, as read or as it would have to be to write.
fn crossedType(check: *Check, crossed: Place.Crossed, writable: bool) Allocator.Error!Pool.Index {
    return switch (crossed.form) {
        .pointer => check.pointerTo(crossed.child, writable),
        .slice => check.sliceOf(crossed.child, writable),
    };
}

/// The place a name reaches. Only a `var` has an address of its own.
fn localPlace(
    check: *const Check,
    node: Node.Index,
    index: Builder.Local.Index,
    text: []const u8,
) Place {
    const local = check.localAt(index);
    const narrow = check.activeNarrow(.{ .local = index });
    if (narrow != null) assert(local.kind != .var_slot);
    return .{
        .kind = if (local.kind == .var_slot) .address else .value,
        .ref = if (narrow) |it| it.ref else local.ref,
        .type = if (narrow) |it| it.type else local.type,
        .node = node,
        .immutable = switch (local.kind) {
            .var_slot => null,
            .let => .let_bound,
            .param => .param_bound,
        },
        .root_name = text,
        .root_node = local.node,
    };
}

fn checkPlace(check: *Check, node: Node.Index) Allocator.Error!?Place {
    if (check.builder == null) {
        const value = try check.checkExpr(node, null);
        return check.placeOfValue(node, value, null);
    }

    switch (check.tree.viewOf(node)) {
        .ident => {
            const text = check.mainTokenText(node);
            if (Module.isDiscard(text)) {
                try check.failDiscard(node);
                return null;
            }
            if (check.findLocalIndex(text)) |index| {
                if (check.localAt(index).type == .poison) return null;
                return check.localPlace(node, index, text);
            }
            const value = try check.checkExpr(node, null);
            return check.placeOfValue(node, value, text);
        },
        .field_access => |access| {
            const base = try check.checkPlace(access.lhs) orelse return null;
            return check.placeField(node, base, access.name_token);
        },
        .deref => |operand| return check.placeThroughPointer(node, operand),
        .bracket => |view| return check.placeIndex(node, view),
        .err => return null,
        else => {
            const value = try check.checkExpr(node, null);
            return check.placeOfValue(node, value, null);
        },
    }
}

fn placeOfValue(
    check: *Check,
    node: Node.Index,
    value: Value,
    name: ?[]const u8,
) Allocator.Error!?Place {
    if (try check.valueOnly(node, value) == false) return null;
    if (value.stops()) return null;
    return .{
        .kind = .value,
        .ref = refOf(value),
        .type = check.typeOf(value),
        .node = node,
        .immutable = if (name == null) .temporary else .let_bound,
        .root_name = name orelse "this value",
        .root_node = node,
    };
}

fn placeThroughPointer(
    check: *Check,
    node: Node.Index,
    operand: Node.Index,
) Allocator.Error!?Place {
    const value = try check.checkValue(operand, null);
    const found = check.typeOf(value);
    if (found == .poison) return null;
    const pointer = try check.pointerAt(node, found, ".*", deref_help) orelse return null;
    return .{
        .kind = .address,
        .ref = refOf(value),
        .type = pointer.child,
        .node = node,
        .immutable = if (pointer.mutable) null else .{
            .read_only = .{ .form = .pointer, .child = pointer.child },
        },
        .root_name = "this pointer",
        .root_node = operand,
    };
}

/// One field step. Crossing a pointer resets mutability to the pointer's own.
fn placeField(
    check: *Check,
    node: Node.Index,
    base: Place,
    name_token: Token.Index,
) Allocator.Error!?Place {
    const comp = check.comp;
    const reached = try check.reachField(base.type, name_token) orelse return null;
    const row = switch (reached.member) {
        .field => |found| found,
        .method => unreachable,
        .length => return check.failNotAPlace(
            name_token,
            "an array's length is in its type, and a view keeps its own",
        ),
        .address => return check.failNotAPlace(
            name_token,
            "a view keeps the address it holds, so write through the view itself",
        ),
    };
    const row_type = comp.rowAt(row).type;

    const through = try check.placeThrough(base, reached.pointer) orelse return null;
    const field_pointer = try check.pointerTo(row_type, through.mutable());
    const place = try check.emit(node, .field_ptr, field_pointer, .{
        .field = .{ .base = through.ref, .row = row },
    });
    return through.reaching(node, place, row_type);
}

fn placeIndex(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Place {
    if (check.rangeIn(view) != null) {
        try check.checkBracketArgs(view);
        try check.fail(node, .{
            .code = .not_assignable,
            .message = "this makes a view, which is a value and not a place",
            .label = "nothing to write to or point at",
        });
        return null;
    }

    const indexed = try check.checkIndex(node, view) orelse return null;
    return check.elementPlace(indexed.elements, indexed.ref);
}

fn elementPlace(check: *Check, elements: Elements, index: Ref) Allocator.Error!?Place {
    assert(elements.child != .poison);
    assert(index != .none);

    const through = try check.elementsThrough(elements) orelse return null;
    if (settledAgainstBase(elements, index) == false) {
        const length = try check.baseLengthRef(elements, through);
        try check.emitCheck(elements.node, .bounds_check, index, length);
    }
    const element_pointer = try check.pointerTo(elements.child, through.mutable());
    const place = try check.emit(elements.node, .elem_ptr, element_pointer, .{
        .bin = .{ .lhs = through.ref, .rhs = index },
    });
    return through.reaching(elements.node, place, elements.child);
}

fn settledAgainstBase(elements: Elements, count: Ref) bool {
    return elements.len != null and refIsConstant(count);
}

fn baseLengthRef(check: *Check, elements: Elements, through: Place) Allocator.Error!Ref {
    const comp = check.comp;
    const count = elements.len orelse
        return check.emitOne(elements.node, .slice_len, .u64_type, through.ref);
    return .fromConstant(try comp.pool.int(comp.gpa, .u64_type, count));
}

fn emitCheck(
    check: *Check,
    node: Node.Index,
    tag: IR.Inst.Tag,
    lhs: Ref,
    rhs: Ref,
) Allocator.Error!void {
    assert(tag == .bounds_check or tag == .order_check);
    _ = try check.emit(node, tag, .void_type, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
}

fn refIsConstant(ref: Ref) bool {
    return ref.unwrap() == .constant;
}

/// A view reaches elements through its value, storage through its place.
fn elementsThrough(check: *Check, elements: Elements) Allocator.Error!?Place {
    if (elements.len != null) return check.placeThrough(elements.base, elements.pointer);

    var held = try check.placeValue(elements.base);
    if (elements.pointer != null) {
        held = try check.emitOne(elements.node, .load, elements.owner, held);
    }
    const base = elements.base.reaching(elements.base.node, held, elements.owner);
    return base.crossing(elements.mutable, .{ .form = .slice, .child = elements.child });
}

fn placeThrough(
    check: *Check,
    base: Place,
    pointer: ?Pool.Key.Pointer,
) Allocator.Error!?Place {
    const it = pointer orelse return check.placeAddress(base);
    const beyond = base.reaching(base.node, try check.placeValue(base), it.child);
    return beyond.crossing(it.mutable, .{ .form = .pointer, .child = it.child });
}

fn placeConstant(check: *const Check, place: Place) ?Pool.Index {
    if (place.kind != .value) return null;
    if (refIsConstant(place.ref) == false) return null;
    const held = place.ref.unwrap().constant;
    return switch (check.comp.pool.keyOf(held)) {
        .value_aggregate, .value_repeat => held,
        else => null,
    };
}

fn failNotAPlace(
    check: *Check,
    name_token: Token.Index,
    help: []const u8,
) Allocator.Error!?Place {
    try check.failToken(name_token, .{
        .code = .not_assignable,
        .message = try check.comp.fmt("'{s}' is a value and not a place", .{
            check.tree.tokenSlice(name_token),
        }),
        .label = "nothing to write to or point at",
        .help = help,
    });
    return null;
}

fn placeValue(check: *Check, place: Place) Allocator.Error!Ref {
    return switch (place.kind) {
        .value => place.ref,
        .address => try check.emitOne(place.node, .load, place.type, place.ref),
    };
}

/// Spills to a temporary, unobservable because only immutable values spill.
fn placeAddress(check: *Check, place: Place) Allocator.Error!?Place {
    if (place.kind == .address) return place;
    if (place.type == .poison) return null;
    assert(place.immutable != null);
    const slot = try check.emitSlot(place.node, .empty, place.type);
    try check.emitStore(place.node, slot, place.ref);
    return place.reaching(place.node, slot, place.type);
}

fn reportImmutable(
    check: *Check,
    node: Node.Index,
    place: Place,
    why: Place.Reason,
) Allocator.Error!void {
    const comp = check.comp;
    const report: Diagnostic.Report = switch (why) {
        .let_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt("'{s}' was bound with 'let', so it cannot change", .{
                place.root_name,
            }),
            .label = "immutable",
            .help = "declare it 'var' if it needs to change",
            .notes = try check.noteHere(place.root_node, "bound here"),
        },
        .param_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt(
                "'{s}' is a parameter, and a parameter is a copy that dies with the call",
                .{place.root_name},
            ),
            .label = "immutable",
            .help = "take '*var T' to write the caller's value, or copy it into a 'var' first",
        },
        .read_only => |crossed| .{
            .code = .write_through_pointer,
            .message = try comp.fmt("this writes through a '{s}', which is read-only", .{
                try comp.typeName(try check.crossedType(crossed, false)),
            }),
            .label = "read-only",
            .help = try comp.fmt("take '{s}' to write through it", .{
                try comp.typeName(try check.crossedType(crossed, true)),
            }),
        },
        .temporary => .{
            .code = .not_assignable,
            .message = "this value has no home, so there is nowhere to write",
            .label = "not a place",
        },
    };
    try check.fail(node, report);
}

pub fn typeOf(check: *const Check, value: Value) Pool.Index {
    return switch (value) {
        .constant => |constant| check.comp.pool.typeOfValue(constant),
        .runtime => |runtime| runtime.type,
        .poison, .diverged => .poison,
        .named_type, .named_generic, .named_fn, .named_module => .poison,
    };
}

pub fn runtimeValue(ref: Ref, type_index: Pool.Index) Value {
    return .{ .runtime = .{ .ref = ref, .type = type_index } };
}

pub fn untypedInt(check: *Check, value: i128) Allocator.Error!Value {
    return .{ .constant = try check.comp.pool.int(check.comp.gpa, .untyped_int_type, value) };
}

pub fn refOf(value: Value) Ref {
    return switch (value) {
        .constant => |constant| .fromConstant(constant),
        .runtime => |runtime| runtime.ref,
        .diverged, .poison => broken_ref,
        .named_type, .named_generic, .named_fn, .named_module => broken_ref,
    };
}

pub fn typeCanHold(check: *const Check, type_index: Pool.Index) bool {
    if (type_index == .void_type) return false;
    if (Pool.isUntyped(type_index)) return false;
    return check.comp.pool.isType(type_index);
}

/// A statement wants void, the one hint that changes a shape.
fn wantsValue(hint: ?Pool.Index) bool {
    const wanted = hint orelse return true;
    return wanted != .void_type;
}

fn tagIsStatement(tag: Node.Tag) bool {
    return switch (tag) {
        .var_decl, .assign, .defer_stmt, .err => true,
        else => false,
    };
}

/// By value for constants, `*var T` where `*T` is asked, membership for unions.
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
                    return check.enterUnion(value, wanted, member, node);
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

fn enterUnion(
    check: *Check,
    value: Value,
    wanted: Pool.Index,
    member: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    // membership settles the second step, so it cannot come back here
    assert(check.comp.pool.unionHas(wanted, member));
    const met = try check.coerce(value, member, node);
    if (met == .poison) return .poison;
    return check.coerce(met, wanted, node);
}

fn failNeedsWritable(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    wanted: Pool.Index,
) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;
    const help: []const u8 = switch (comp.pool.keyOf(wanted)) {
        .type_slice => "take '[]var' where the view is made",
        else => "take '*var' where the pointer is made",
    };
    try check.fail(node, .{
        .code = .write_through_pointer,
        .message = try comp.fmt("this is {s}, and {s} is needed to write", .{
            try comp.typeName(found),
            try comp.typeName(wanted),
        }),
        .label = "read-only",
        .help = help,
    });
}

fn fitValue(
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

fn doesNotFit(
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
    const found_name = try comp.typeName(found);

    const narrowable = found != .poison and wanted != .poison and
        comp.pool.isUnion(found) and comp.pool.subsumes(found, wanted);
    const help: []const u8 = help: {
        if (narrowable) break :help narrow_help;
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
            found_name,
        }),
        .label = "the wrong type",
        .help = help,
    });
}

/// Whether the value is one. A name is reported here.
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

pub fn checkValue(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const value = try check.checkExpr(node, hint);
    return if (try check.valueOnly(node, value)) value else .poison;
}

/// What never settles. A branch is not here, because a settled one picks its arm.
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

fn reportBadOperand(
    check: *Check,
    op_token: Token.Index,
    operand_type: Pool.Index,
) Allocator.Error!void {
    const tag = check.tree.tokenTag(op_token);
    const equality = tag == .eq_eq or tag == .bang_eq;
    try check.failToken(op_token, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'{s}' cannot be applied to {s}", .{
            check.tree.tokenSlice(op_token),
            try check.comp.typeName(operand_type),
        }),
        .label = "wrong operand type",
        .help = check.operandHelp(operand_type, equality),
    });
}

fn operandHelp(check: *const Check, found: Pool.Index, equality: bool) ?[]const u8 {
    const pool = &check.comp.pool;
    if (pool.isUnion(found)) {
        if (equality) return "'is' tests which member a union holds and narrows the name to it";
        for (pool.unionMembers(found)) |member| {
            if (Pool.isNumeric(member) or pool.keyOf(member) == .type_pointer) {
                return "narrow it first, with 'match' or a guard 'is T or return', " ++
                    "and never through a 'var'";
            }
        }
        return null;
    }
    if (equality == false) return null;
    return switch (check.comp.pool.keyOf(found)) {
        .type_slice => "'std.mem.eql' compares two views element by element",
        .type_array => "slice them first, as in 'mem.eql(a[0..], b[0..])'",
        .type_struct => "compare the fields that decide it",
        else => null,
    };
}

fn failDiscard(check: *Check, node: Node.Index) Allocator.Error!void {
    try check.fail(node, .{
        .code = .discard_reserved,
        .message = "'_' is not a name, and only discards a value",
        .label = "not a name",
        .help = "write '_ = expression' to drop a value on purpose",
    });
}

fn reportUndefined(check: *Check, node: Node.Index, text: []const u8) Allocator.Error!void {
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
    comp.considerDecls(&closest, check.module.decls);
    if (comp.prelude) |prelude| {
        if (prelude != check.module_index) {
            comp.considerDecls(&closest, comp.moduleAt(prelude).decls);
        }
    }
    for (Pool.primitive_names) |name| closest.consider(name);

    return comp.didYouMean(closest);
}

pub fn origin(check: *const Check, node: Node.Index) Compilation.Origin {
    return .{ .module = check.module_index, .node = node };
}

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

fn noteHere(
    check: *Check,
    node: Node.Index,
    message: []const u8,
) Allocator.Error![]Diagnostic.Note {
    return check.comp.noteOne(check.module_index, node, message);
}

const block_dead = std.math.maxInt(u32);

/// Blocks nothing jumps to are dropped, then the body is committed to the shared tables.
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

    const blocks_start: u32 = @intCast(comp.blocks.items.len);
    try comp.blocks.ensureUnusedCapacity(gpa, live_blocks);
    for (builder.blocks.items, map) |block, slot| {
        if (slot == block_dead) continue;
        comp.blocks.appendAssumeCapacity(.{
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
    if (comp.insts.len + inst_count > std.math.maxInt(u32)) return error.OutOfMemory;
    const insts_start: u32 = @intCast(comp.insts.len);
    try comp.insts.resize(gpa, comp.insts.len + inst_count);
    const from = builder.insts.slice();
    const into = comp.insts.slice();
    inline for (std.enums.values(IR.InstList.Field)) |column| {
        @memcpy(into.items(column)[insts_start..], from.items(column));
    }

    // the pair of the range assertion `emit` makes on the way in
    const tree_nodes = check.tree.nodes.len;
    for (into.items(.node)[insts_start..]) |node| assert(node.int() < tree_nodes);

    const extra_start: u32 = @intCast(comp.inst_extra.items.len);
    try comp.inst_extra.appendSlice(gpa, builder.extra.items);

    try comp.commitFunc(.{
        .instance = builder.instance,
        .insts = .since(insts_start, comp.insts.len),
        .extra = .since(extra_start, comp.inst_extra.items.len),
        .blocks = .since(blocks_start, comp.blocks.items.len),
    });
}

fn finishFuncVisit(map: []u32, frontier: *std.ArrayList(u32), target: u32) void {
    if (map[target] != block_dead) return;
    map[target] = 0;
    frontier.appendAssumeCapacity(target);
}

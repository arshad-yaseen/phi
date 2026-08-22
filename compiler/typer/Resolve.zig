const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Compilation = @import("../Compilation.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");

const Decl = Module.Decl;
const Node = AST.Node;
const Value = Typer.Value;
const Binding = Typer.Binding;
const type_params_max = Typer.type_params_max;
const bindings_max = Typer.bindings_max;

pub fn typeParamNodes(comp: *const Compilation, decl_index: Decl.Index) [2][]const Node.Index {
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

pub fn bindTypeParams(
    typer: *Typer,
    instance: Pool.Instance,
    buffer: *[bindings_max]Binding,
) Allocator.Error!void {
    const comp = typer.comp;
    assert(typer.bindings.len == 0);
    const decl_index = comp.instanceDecl(instance);
    const where = comp.declAt(decl_index).origin();

    // bounds first, because resolving one can move the arguments
    var bounds: [bindings_max]Pool.Index = undefined;
    var count: u32 = 0;
    for ([_]Decl.OptionalIndex{ comp.declAt(decl_index).owner, decl_index.toOptional() }) |owned| {
        const index = owned.unwrap() orelse continue;
        var found: [type_params_max]Pool.Index = undefined;
        const resolved = try comp.boundsOf(index, where, &found) orelse &.{};
        for (0..comp.declAt(index).type_params) |at| {
            bounds[count] = boundAt(resolved, at) orelse .poison;
            count += 1;
        }
    }

    const args = comp.instanceArgs(instance);
    assert(count == args.len);
    var at: u32 = 0;
    for (typeParamNodes(comp, decl_index)) |list| {
        for (list) |param| {
            buffer[at] = .{
                .name = try comp.pool.string(comp.gpa, typer.mainTokenText(param)),
                .type = args[at],
                .bound = boundAt(&bounds, at),
            };
            at += 1;
        }
    }
    assert(at == count);
    typer.bindings = buffer[0..count];
}

pub fn boundAt(bounds: []const Pool.Index, at: usize) ?Pool.Index {
    if (at >= bounds.len) return null;
    return if (bounds[at] == .poison) null else bounds[at];
}

pub fn boundOf(typer: *Typer, decl_index: Decl.Index, param: Node.Index) Allocator.Error!?Pool.Index {
    assert(typer.bindings.len == 0);
    if (typer.tree.nodeTag(param) != .type_param) return null;
    const written = typer.tree.viewOf(param).type_param.bound.unwrap() orelse return null;

    if (typer.tree.nodeTag(written) == .ident) {
        for (typeParamNodes(typer.comp, decl_index)) |list| {
            for (list) |other| {
                if (typer.tree.nodeTag(other) != .type_param) continue;
                const other_name = typer.mainTokenText(other);
                if (std.mem.eql(u8, other_name, typer.mainTokenText(written)) == false) continue;
                try typer.fail(written, .{
                    .code = .not_a_type,
                    .message = try typer.comp.fmt("a bound names concrete types, and '{s}' " ++
                        "is a type parameter", .{other_name}),
                    .label = "not concrete",
                });
                return null;
            }
        }
    }
    const bound = try resolveType(typer, written);
    return if (bound == .poison) null else bound;
}

pub fn unionBoundOfName(typer: *const Typer, node: Node.Index) ?Pool.Index {
    if (typer.tree.nodeTag(node) != .ident) return null;
    const text = typer.mainTokenText(node);
    for (typer.bindings) |binding| {
        if (typer.comp.pool.sameText(binding.name, text) == false) continue;
        const bound = binding.bound orelse return null;
        return if (typer.comp.pool.isUnion(bound)) bound else null;
    }
    return null;
}

/// A union bound admits its members, never a union.
fn withinBound(pool: *const Pool, bound: Pool.Index, type_index: Pool.Index) bool {
    if (pool.isUnion(bound)) return pool.unionHas(bound, type_index);
    return bound == type_index;
}

pub fn admittedBy(
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

pub fn boundsHold(
    typer: *Typer,
    decl_index: Decl.Index,
    args: []const Pool.Index,
    node: Node.Index,
) Allocator.Error!bool {
    const comp = typer.comp;
    var found: [type_params_max]Pool.Index = undefined;
    const bounds = try comp.boundsOf(decl_index, typer.origin(node), &found) orelse return true;
    const decl = comp.declAt(decl_index);
    const params = typeParamNodes(comp, decl_index)[1];
    assert(params.len == args.len);
    assert(bounds.len == args.len);

    for (params, args, bounds) |param, arg, bound| {
        if (bound == .poison) continue;
        if (withinBound(&comp.pool, bound, arg)) continue;
        const tree = comp.treeOf(decl.module);
        try typer.fail(node, .{
            .code = .not_a_member,
            .message = try comp.fmt("'{s}' is not a member of '{s}', which bounds '{s}'", .{
                try comp.typeName(arg),
                try comp.typeName(bound),
                tree.tokenSlice(tree.nodeMainToken(param)),
            }),
            .label = "outside the bound",
            .notes = try comp.noteOne(decl.module, param, "bounded here"),
        });
        return false;
    }
    return true;
}

pub fn resolveWrittenType(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    const resolved = try resolveType(typer, node);
    if (typer.demand_embedding and resolved != .poison) {
        try Typer.walkEmbedded(typer.comp, resolved, typer.origin(node), 0);
    }
    return resolved;
}

pub fn resolveType(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    switch (typer.tree.viewOf(node)) {
        .ident => return resolveTypeName(typer, node),
        .field_access => |access| switch (try typer.checkExpr(access.lhs, null)) {
            .named_module => |target| {
                const member = try exported(typer, target, node, access.name_token) orelse
                    return .poison;
                return declAsType(typer, member, node);
            },
            .poison => return .poison,
            else => {
                try typer.fail(node, .{
                    .code = .not_a_type,
                    .message = "only a module reaches a type with '.'",
                    .label = "not a type",
                });
                return .poison;
            },
        },
        .bracket => return resolveBracketType(typer, node),
        .array_type => |array| return resolveArrayType(typer, array),
        .slice_type => |slice| {
            const child = try resolveType(typer, slice.child);
            if (child == .poison) return .poison;
            return typer.sliceOf(child, slice.is_mutable);
        },
        .pointer_type => |pointer| {
            const child = try resolveType(typer, pointer.child);
            if (child == .poison) return .poison;
            return typer.pointerTo(child, pointer.is_mutable);
        },
        .union_type => |members| return resolveUnionType(typer, node, members),
        .match_expr => if (try resolveMatchType(typer, node)) |found| return found,
        .binary => |it| if (it.op == .bit_or) return resolveOrType(typer, node, it),
        .err => return .poison,
        else => {},
    }
    try typer.fail(node, .{
        .code = .not_a_type,
        .message = "this is a value, and a type belongs here",
        .label = "not a type",
    });
    return .poison;
}

fn resolveMatchType(typer: *Typer, node: Node.Index) Allocator.Error!?Pool.Index {
    const chosen = try typer.checkExpr(node, null);
    if (chosen.stops()) return .poison;
    return namedType(typer, node, chosen);
}

fn resolveArrayType(typer: *Typer, view: AST.View.ArrayType) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    const length = try arrayLength(typer, view.length);
    const child = try resolveType(typer, view.child);
    if (child == .poison) return .poison;
    const count = length orelse return .poison;
    return comp.pool.intern(comp.gpa, .{ .type_array = .{ .child = child, .len = count } });
}

fn arrayLength(typer: *Typer, node: Node.Index) Allocator.Error!?u64 {
    const value = try typer.checkValue(node, .u64_type);
    if (value.stops()) return null;
    if (value == .runtime) {
        try typer.fail(node, .{
            .code = .not_constant,
            .message = "an array's length is part of its type, so it is known " ++
                "before anything runs",
            .label = "not a constant",
            .help = "write the length itself, or another array's length",
        });
        return null;
    }

    const met = try typer.fitValue(value.constant, .u64_type, node);
    if (met != .constant) return null;

    const folded = typer.comp.pool.keyOf(met.constant).value_int;
    assert(folded.type == .u64_type);
    assert(folded.value >= 0);
    return @intCast(folded.value);
}

fn resolveUnionType(
    typer: *Typer,
    node: Node.Index,
    members: []const Node.Index,
) Allocator.Error!Pool.Index {
    assert(members.len >= 2);
    if (members.len > Pool.union_members_max) {
        try failTooWide(typer, node);
        return .poison;
    }

    var buffer: [Pool.union_members_max]Pool.Index = undefined;
    var clean = true;
    for (members, 0..) |member, at| {
        buffer[at] = try resolveType(typer, member);
        if (buffer[at] == .poison) clean = false;
    }
    if (clean == false) return .poison;
    return uniteResolved(typer, node, buffer[0..members.len], members);
}

fn uniteResolved(
    typer: *Typer,
    node: Node.Index,
    resolved: []const Pool.Index,
    written: []const Node.Index,
) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    switch (try comp.pool.unite(comp.gpa, resolved)) {
        .index => |index| return index,
        .duplicate => |repeat| {
            var where = node;
            for (written, 0..) |member, at| {
                if (resolved[at] == repeat) where = member;
            }
            try typer.fail(where, .{
                .code = .duplicate_member,
                .message = try comp.fmt("'{s}' is already a member of this union", .{
                    try comp.typeName(repeat),
                }),
                .label = "the same type again",
                .help = "members are distinct types, and an alias is not a new type",
            });
        },
        .too_wide => try failTooWide(typer, node),
    }
    return .poison;
}

fn failGenericBare(typer: *Typer, node: Node.Index, name: []const u8) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .generic_arguments,
        .message = try typer.comp.fmt("'{s}' is generic, so it needs its arguments", .{name}),
        .label = "no arguments here",
        .help = try typer.comp.fmt("write '{s}[...]' with one type per parameter", .{name}),
    });
}

fn resolveOrType(
    typer: *Typer,
    node: Node.Index,
    it: AST.View.Binary,
) Allocator.Error!Pool.Index {
    assert(it.op == .bit_or);
    const lhs = try resolveType(typer, it.lhs);
    const rhs = try resolveType(typer, it.rhs);
    if (lhs == .poison or rhs == .poison) return .poison;
    return uniteResolved(typer, node, &.{ lhs, rhs }, &.{});
}

fn failTooWide(typer: *Typer, node: Node.Index) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .union_too_wide,
        .message = try typer.comp.fmt("flat, a union holds at most {d} members", .{
            Pool.union_members_max,
        }),
        .label = "too wide",
    });
}

fn resolveTypeName(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    const text = typer.mainTokenText(node);
    for (typer.bindings) |binding| {
        if (typer.comp.pool.sameText(binding.name, text)) return binding.type;
    }
    if (Pool.primitiveType(text)) |primitive| return primitive;
    const decl_index = visibleDecl(typer, text) orelse {
        try typer.reportUndefined(node, text);
        return .poison;
    };
    return declAsType(typer, decl_index, node);
}

pub fn visibleDecl(typer: *const Typer, text: []const u8) ?Decl.Index {
    if (typer.module.findDecl(text)) |own| return own;

    const comp = typer.comp;
    const prelude = comp.prelude orelse return null;
    if (prelude == typer.module_index) return null;

    const found = comp.moduleAt(prelude).findDecl(text) orelse return null;
    if (Module.declIsPub(comp, found) == false) return null;
    return found;
}

pub fn exported(
    typer: *Typer,
    target: Module.Index,
    node: Node.Index,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    return Module.findExported(typer.comp, target, typer.origin(node), name_token);
}

fn ensured(typer: *Typer, decl_index: Decl.Index, node: Node.Index) Allocator.Error!?Decl {
    try typer.comp.ensure(.{ .decl = decl_index }, typer.origin(node));
    const decl = typer.comp.declAt(decl_index);
    return if (decl.state == .done) decl else null;
}

pub fn declAsType(typer: *Typer, decl_index: Decl.Index, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    const decl = comp.declAt(decl_index);
    const name = comp.pool.stringText(decl.name);

    switch (decl.kind) {
        .struct_decl, .type_alias => {
            if (comp.declAt(decl_index).type_params > 0) {
                try failGenericBare(typer, node, name);
                return .poison;
            }
            if (decl.kind == .struct_decl) {
                const instance = try comp.instantiate(decl_index, &.{}, typer.origin(node));
                return comp.instanceType(instance);
            }
            const settled = try ensured(typer, decl_index, node) orelse return .poison;
            return settled.answer.type;
        },
        .unit_decl => {
            assert(comp.declAt(decl_index).type_params == 0);
            return comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
        },
        .import => {
            if (try ensured(typer, decl_index, node) == null) return .poison;
            try typer.fail(node, .{
                .code = .not_a_type,
                .message = try comp.fmt("'{s}' is a module, not a type", .{name}),
                .label = "a module",
                .help = "name a type inside it",
            });
            return .poison;
        },
        .let, .fn_decl, .extern_fn => {
            const what: []const u8 = if (decl.kind == .let) "a value" else "a function";
            try typer.fail(node, .{
                .code = .not_a_type,
                .message = try comp.fmt("'{s}' is {s}, not a type", .{ name, what }),
                .label = "not a type",
            });
            return .poison;
        },
    }
}

pub fn resolveBracketType(typer: *Typer, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = typer.comp;
    const view = typer.tree.viewOf(node).bracket;

    const base = try typer.checkExpr(view.base, null);
    const decl_index = switch (base) {
        .named_generic => |decl_index| decl_index,
        .named_type, .named_fn => {
            try typer.fail(node, .{
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
            try typer.fail(view.base, .{
                .code = .not_a_type,
                .message = "only a generic struct takes type arguments here",
                .label = "not a generic type",
            });
            return .poison;
        },
    };

    const wanted = comp.declAt(decl_index).type_params;
    if (view.args.len != wanted) {
        const name = comp.pool.stringText(comp.declAt(decl_index).name);
        try typer.failArity(node, name, .type, wanted, view.args.len, &.{});
        return .poison;
    }

    var args_buffer: [type_params_max]Pool.Index = undefined;
    const args = args_buffer[0..view.args.len];
    for (view.args, args) |arg, *resolved| {
        resolved.* = try resolveType(typer, arg);
        if (resolved.* == .poison) return .poison;
    }
    if (try boundsHold(typer, decl_index, args, node) == false) return .poison;

    const instance = try comp.instantiate(decl_index, args, typer.origin(node));
    if (comp.declAt(decl_index).kind == .type_alias) {
        try comp.ensure(.{ .head = instance }, typer.origin(node));
        if (comp.instanceAt(instance).head != .done) return .poison;
    }
    return comp.instanceType(instance);
}

pub fn namedType(typer: *Typer, node: Node.Index, value: Value) Allocator.Error!?Pool.Index {
    switch (value) {
        .named_type => |type_index| return type_index,
        .named_generic => |decl_index| {
            const decl = typer.comp.declAt(decl_index);
            try failGenericBare(typer, node, typer.comp.pool.stringText(decl.name));
            return .poison;
        },
        else => return null,
    }
}

pub fn declAsValue(typer: *Typer, decl_index: Decl.Index, node: Node.Index) Allocator.Error!Value {
    const comp = typer.comp;
    const decl = comp.declAt(decl_index);
    switch (decl.kind) {
        .let => {
            const settled = try ensured(typer, decl_index, node) orelse return .poison;
            return .{ .constant = settled.answer.constant };
        },
        .fn_decl => return .{ .named_fn = decl_index },
        .extern_fn => {
            if (try ensured(typer, decl_index, node) == null) return .poison;
            return .{ .named_fn = decl_index };
        },
        .struct_decl => {
            if (comp.declAt(decl_index).type_params > 0) return .{ .named_generic = decl_index };
            const instance = try comp.instantiate(decl_index, &.{}, typer.origin(node));
            return .{ .named_type = comp.instanceType(instance) };
        },
        .type_alias => {
            if (comp.declAt(decl_index).type_params > 0) return .{ .named_generic = decl_index };
            const settled = try ensured(typer, decl_index, node) orelse return .poison;
            return .{ .named_type = settled.answer.type };
        },
        .unit_decl => {
            const unit_type = try comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
            return .{ .constant = try comp.pool.unitValue(comp.gpa, unit_type) };
        },
        .import => {
            if (try ensured(typer, decl_index, node) == null) return .poison;
            return .{ .named_module = Module.importedModule(comp, decl_index) };
        },
    }
}

//! Type check the AST, lowering function bodies to IR.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Compilation = @import("Compilation.zig");
const IR = @import("IR.zig");
const Layout = @import("Layout.zig");
const Module = @import("Module.zig");
const Pool = @import("Pool.zig");
const Builtin = @import("Builtin.zig").Builtin;
const Token = @import("Token.zig");
const handle = @import("util/handle.zig");
const number = @import("util/number.zig");
const spell = @import("util/spell.zig");
const literal = @import("util/text.zig");

const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;

comp: *Compilation,
module_index: Module.Index,
module: *Module,
tree: *const AST,
/// The type parameters in scope, substituted for the whole unit.
bindings: []const Binding,
/// Null means constants only.
builder: ?*Builder,
/// The module's `bool` and `none` once found, `.poison` until then.
bool_type: Pool.Index,
none_type: Pool.Index,
/// Field types skip the embedding demand, because their struct gets its own walk.
demand_embedding: bool,

const Check = @This();

/// The body under check. Only constants-only mode has none.
fn body(check: *const Check) *Builder {
    return check.builder.?;
}

const type_params_max = AST.type_params_max;
const bindings_max = type_params_max * 2;
const call_args_max = 255;
const type_depth_max = AST.nest_max;

const Binding = struct { name: Pool.String, type: Pool.Index };

/// One part of a literal or one call argument. `initializer` is `.none` outside a literal.
pub const Operand = struct { value: Value, initializer: Node.OptionalIndex };

/// What an expression turned out to be. A `named_` case is not a value.
pub const Value = union(enum) {
    constant: Pool.Index,
    runtime: Runtime,
    /// No value, no diagnostic owed. `poison` is the same after one.
    diverged,
    poison,
    /// `Point` in `Point.zero()`.
    named_type: Pool.Index,
    /// `Box` in `Box[i64]`, awaiting arguments.
    named_generic: Decl.Index,
    /// `helper` in `helper(1)`.
    named_fn: Decl.Index,
    /// `std` in `std.mem`.
    named_module: Module.Index,

    const Runtime = struct { ref: Ref, type: Pool.Index };

    /// A void result. Callers read the type, never the ref.
    const void_value: Value = .{
        .runtime = .{ .ref = .fromConstant(.poison), .type = .void_type },
    };
};

// entry points, one per unit kind `ensure` dispatches

pub fn typeAlias(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index, &.{});
    const view = check.tree.viewOf(check.declNode(decl_index)).alias_decl;

    const resolved = try check.resolveWrittenType(view.aliased);
    comp.declPtr(decl_index).result = resolved.int();
    return resolved != .poison;
}

/// The aliased type with this instantiation's arguments bound.
pub fn aliasInstance(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    assert(comp.declAt(decl_index).kind == .type_alias);

    var buffer: [bindings_max]Binding = undefined;
    const bindings = try bindTypeParams(comp, instance, &buffer);
    var check = context(comp, decl_index, bindings);

    const view = check.tree.viewOf(check.declNode(decl_index)).alias_decl;
    const resolved = try check.resolveWrittenType(view.aliased);
    comp.instancePtr(instance).type = resolved;
    return resolved != .poison;
}

pub fn topLevelLet(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index, &.{});
    const view = check.tree.viewOf(check.declNode(decl_index)).var_decl;
    // a top-level 'var' was already refused by the parser, and checks as 'let'

    // resolved before the value, so a literal can land on what it says
    const annotation: ?Pool.Index = if (view.type_expr.unwrap()) |type_expr|
        try check.resolveType(type_expr)
    else
        null;

    const value = try check.checkExpr(view.init_expr, annotation);
    const constant = switch (value) {
        .constant => |index| index,
        .poison => Pool.Index.poison,
        .runtime => unreachable,
        else => other: {
            try check.reportNotValue(view.init_expr, value);
            break :other Pool.Index.poison;
        },
    };

    var met = constant;
    if (annotation) |wanted| {
        met = switch (try check.fitValue(constant, wanted, view.init_expr)) {
            .constant => |final| final,
            else => .poison,
        };
    }

    comp.declPtr(decl_index).result = met.int();
    return met != .poison;
}

/// Fields into rows, with the type parameters bound to this instantiation.
pub fn structRows(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    var buffer: [bindings_max]Binding = undefined;
    const bindings = try bindTypeParams(comp, instance, &buffer);
    var check = context(comp, decl_index, bindings);
    check.demand_embedding = false;

    const view = check.tree.viewOf(check.declNode(decl_index)).struct_decl;

    // staged, because resolving a field type can build other rows
    const mark = comp.rows_scratch.items.len;
    defer comp.rows_scratch.shrinkRetainingCapacity(mark);

    var clean = true;
    for (view.members) |member| {
        if (check.tree.nodeTag(member) != .field) continue;
        const field = check.tree.viewOf(member).field;

        const field_type = try check.resolveType(field.type_expr);
        if (field_type == .poison) clean = false;
        try comp.rows_scratch.append(comp.gpa, .{
            .name = try comp.pool.string(comp.gpa, check.tree.tokenSlice(field.name_token)),
            .type = field_type,
            .node = member,
        });
    }

    try commitRows(comp, instance, mark);
    return clean;
}

fn commitRows(comp: *Compilation, instance: Pool.Instance, mark: usize) Allocator.Error!void {
    const staged = comp.rows_scratch.items[mark..];
    if (comp.rows.items.len + staged.len > std.math.maxInt(u32)) return error.OutOfMemory;

    const rows_start: u32 = @intCast(comp.rows.items.len);
    try comp.rows.appendSlice(comp.gpa, staged);
    comp.instancePtr(instance).rows = .{ .start = rows_start, .len = @intCast(staged.len) };
}

/// What a struct embeds by value. A cycle means no size, which `ensure` reports.
pub fn structEmbedding(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    const decl = comp.declAt(decl_index);
    const from: Compilation.Origin = .{ .module = decl.module, .node = decl.node };
    try comp.ensure(.of(.rows, instance), from);

    const rows = comp.instanceAt(instance).rows;
    for (rows.start..rows.end()) |raw| {
        // by index, because the walk can grow the rows table
        const row = comp.rowAt(.from(raw));
        try walkEmbedded(comp, row.type, .{ .module = decl.module, .node = row.node }, 0);
    }
    return true;
}

/// The types a value embeds directly. A pointer breaks the chain.
fn walkEmbedded(
    comp: *Compilation,
    type_index: Pool.Index,
    from: Compilation.Origin,
    depth: u32,
) Allocator.Error!void {
    if (depth >= type_depth_max) return;
    switch (comp.pool.keyOf(type_index)) {
        .type_struct => |embedded| try comp.ensure(.of(.embedding, embedded), from),
        // every element embeds, so an array of a type is a cycle through it
        .type_array => |array| try walkEmbedded(comp, array.child, from, depth + 1),
        .type_union => {
            // every member embeds in place, read by position because the demand interns
            const count = comp.pool.unionMemberCount(type_index);
            var at: u32 = 0;
            while (at < count) : (at += 1) {
                const member = comp.pool.unionMemberAt(type_index, at);
                try walkEmbedded(comp, member, from, depth + 1);
            }
        },
        .type_simple, .type_unit, .type_pointer, .type_slice => {},
        .value_int, .value_float, .value_aggregate => unreachable,
        .value_unit, .value_union, .value_slice, .value_splat => unreachable,
    }
}

pub fn externDecl(comp: *Compilation, decl_index: Decl.Index) Allocator.Error!bool {
    var check = context(comp, decl_index, &.{});
    const view = check.tree.viewOf(check.declNode(decl_index)).fn_decl;
    const name = comp.pool.stringText(comp.declAt(decl_index).name);

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
            .message = try comp.fmt("'{s}' is generic, and one symbol has one signature", .{name}),
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
        // a view is niched too, and two words wide either way
        .type_union => union_help: {
            const carrier = Layout.niche(&comp.pool, found) orelse
                break :union_help extern_union_help;
            if (comp.pool.keyOf(carrier) == .type_pointer) return true;
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
    const bindings = try bindTypeParams(comp, instance, &buffer);
    var check = context(comp, decl_index, bindings);

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
            if (comp.pool.sameText(earlier.name, name_text)) {
                try check.fail(param_node, .{
                    .code = .redeclared,
                    .message = try comp.fmt("'{s}' is already a parameter", .{name_text}),
                    .label = "declared again here",
                    .notes = try comp.notes(&.{
                        comp.noteAt(check.module_index, earlier.node, "first declared here"),
                    }),
                });
                clean = false;
                break;
            }
        }

        if (view.is_extern) {
            if (try check.externCrosses(param_node, param_type, "parameter") == false) {
                clean = false;
            }
        }

        try comp.rows_scratch.append(comp.gpa, .{
            .name = try comp.pool.string(comp.gpa, name_text),
            .type = param_type,
            .node = param_node,
        });
    }

    try commitRows(comp, instance, mark);

    const return_type: Pool.Index = if (view.return_type.unwrap()) |type_expr|
        try check.resolveWrittenType(type_expr)
    else
        .void_type;
    comp.instancePtr(instance).type = return_type;

    // returning nothing always crosses, so only a written type is checked
    if (view.is_extern) {
        if (view.return_type.unwrap()) |type_expr| {
            if (try check.externCrosses(type_expr, return_type, "return type") == false) {
                clean = false;
            }
        }
    }

    if (return_type == .poison) clean = false;
    return clean;
}

/// Arguments to type parameters, the owner first for a member.
fn bindTypeParams(
    comp: *Compilation,
    instance: Pool.Instance,
    buffer: *[bindings_max]Binding,
) Allocator.Error![]const Binding {
    const decl_index = comp.instanceDecl(instance);
    const decl = comp.declAt(decl_index);
    const args = comp.instanceArgs(instance);
    const tree = comp.treeOf(decl.module);

    const owner_params: []const Node.Index = if (decl.owner.unwrap()) |owner_index|
        tree.viewOf(comp.declAt(owner_index).node).struct_decl.type_params
    else
        &.{};
    const own = switch (tree.viewOf(decl.node)) {
        .struct_decl => |view| view.type_params,
        .fn_decl => |view| view.type_params,
        .alias_decl => |view| view.type_params,
        else => unreachable,
    };

    var count: u32 = 0;
    for ([_][]const Node.Index{ owner_params, own }) |params| {
        assert(params.len <= type_params_max);
        for (params) |param| {
            assert(count < buffer.len);
            buffer[count] = .{
                .name = try comp.pool.string(comp.gpa, tree.tokenSlice(tree.nodeMainToken(param))),
                .type = args[count],
            };
            count += 1;
        }
    }

    assert(count == args.len);
    return buffer[0..count];
}

fn context(comp: *Compilation, decl_index: Decl.Index, bindings: []const Binding) Check {
    const decl = comp.declAt(decl_index);
    const module = comp.moduleAt(decl.module);
    return .{
        .comp = comp,
        .module_index = decl.module,
        .module = module,
        .tree = &module.tree,
        .bindings = bindings,
        .builder = null,
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

// type expressions, where the type grammar meets the pool

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
        .field_access => |access| {
            const base = try check.checkExpr(access.lhs, null);
            switch (base) {
                .named_module => |target| {
                    const member = try check.moduleMember(target, node, access.name_token) orelse
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
            }
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
        // `A | B` in a bracket arrives as an expression, and means the union
        .binary => |it| if (it.op == .bit_or) return check.resolveOrType(node, it),
        .err => return .poison,
        // a bracket item arrives as an expression until its base says otherwise
        else => {},
    }

    try check.fail(node, .{
        .code = .not_a_type,
        .message = "this is a value, and a type belongs here",
        .label = "not a type",
    });
    return .poison;
}

pub fn pointerTo(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
    const comp = check.comp;
    return comp.pool.intern(comp.gpa, .{ .type_pointer = .{ .child = child, .mutable = mutable } });
}

fn sliceOf(check: *Check, child: Pool.Index, mutable: bool) Allocator.Error!Pool.Index {
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

/// The N in `[N]T`, settled before anything runs. Null once reported.
fn arrayLength(check: *Check, node: Node.Index) Allocator.Error!?u64 {
    const comp = check.comp;

    const value = try check.checkExpr(node, .u64_type);
    switch (value) {
        .constant => {},
        .poison, .diverged => return null,
        .runtime => {
            try check.fail(node, .{
                .code = .not_constant,
                .message = "an array's length is part of its type, so it is known " ++
                    "before anything runs",
                .label = "not a constant",
                .help = "write the length itself, or another array's length",
            });
            return null;
        },
        else => {
            try check.reportNotValue(node, value);
            return null;
        },
    }

    // a count, so the refusals a `u64` already makes are the refusals here
    const met = try check.fitValue(value.constant, .u64_type, node);

    if (met != .constant) return null;

    const folded = comp.pool.keyOf(met.constant).value_int;

    assert(folded.type == .u64_type);
    assert(folded.value >= 0);
    return @intCast(folded.value);
}

fn resolveUnionType(
    check: *Check,
    node: Node.Index,
    members: []const Node.Index,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    assert(members.len >= 2);

    if (members.len > Pool.union_members_max) {
        try check.failTooWide(node);
        return .poison;
    }

    var buffer: [Pool.union_members_max]Pool.Index = undefined;
    var clean = true;
    for (members, 0..) |member, at| {
        const resolved = try check.resolveType(member);
        if (resolved == .poison) clean = false;
        buffer[at] = resolved;
    }
    if (clean == false) return .poison;

    switch (try comp.pool.unite(comp.gpa, buffer[0..members.len])) {
        .index => |index| return index,
        .duplicate => |repeat| {
            // the caret prefers the member written twice over the whole union
            var where = node;
            for (members, 0..) |member, at| {
                if (buffer[at] == repeat) where = member;
            }
            return check.failDuplicateMember(where, repeat);
        },
        .too_wide => {
            try check.failTooWide(node);
            return .poison;
        },
    }
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
    const comp = check.comp;

    const lhs = try check.resolveType(it.lhs);
    const rhs = try check.resolveType(it.rhs);
    if (lhs == .poison) return .poison;
    if (rhs == .poison) return .poison;

    // `a | b | c` recursed on the left into a union, and the splice flattens it
    switch (try comp.pool.unite(comp.gpa, &.{ lhs, rhs })) {
        .index => |index| return index,
        .duplicate => |repeat| return check.failDuplicateMember(node, repeat),
        .too_wide => {
            try check.failTooWide(node);
            return .poison;
        },
    }
}

fn failDuplicateMember(
    check: *Check,
    node: Node.Index,
    repeat: Pool.Index,
) Allocator.Error!Pool.Index {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .duplicate_member,
        .message = try check.comp.fmt("'{s}' is already a member of this union", .{
            try check.comp.typeName(repeat),
        }),
        .label = "the same type again",
        .help = "members are distinct types, and an alias is not a new type",
    });
    return .poison;
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

/// The declaration a bare name reaches here, the file's own or the prelude's public.
fn visibleDecl(check: *const Check, text: []const u8) ?Decl.Index {
    if (check.module.findDecl(text)) |own| return own;

    const comp = check.comp;
    const prelude = comp.prelude orelse return null;
    if (prelude == check.module_index) return null;

    const found = comp.moduleAt(prelude).findDecl(text) orelse return null;
    if (Module.declIsPub(comp, found) == false) return null;
    return found;
}

/// Analyzed on demand. Null is poisoned, already reported.
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
        .struct_decl => {
            if (comp.typeParamCount(decl_index) > 0) {
                try check.failGenericBare(node, name);
                return .poison;
            }
            const instance = try comp.instantiate(decl_index, &.{}, check.origin(node));
            return comp.instanceType(instance);
        },
        .type_alias => {
            if (comp.typeParamCount(decl_index) > 0) {
                try check.failGenericBare(node, name);
                return .poison;
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
            switch (Module.importTarget(comp, decl_index)) {
                .decl => |target| return check.declAsType(target, node),
                .module => {
                    try check.fail(node, .{
                        .code = .not_a_type,
                        .message = try comp.fmt("'{s}' is a module, not a type", .{name}),
                        .label = "a module",
                        .help = "name a type inside it",
                    });
                    return .poison;
                },
            }
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

/// Needs the base to name a generic struct or a generic alias.
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
        try check.fail(node, .{
            .code = .generic_arguments,
            .message = try comp.fmt("'{s}' takes {d} type argument{s}, and this writes {d}", .{
                name, wanted, plural(wanted), view.args.len,
            }),
            .label = "wrong number of arguments",
        });
        return .poison;
    }

    var args_buffer: [type_params_max]Pool.Index = undefined;
    assert(view.args.len <= args_buffer.len);
    for (view.args, 0..) |arg, position| {
        const resolved = try check.resolveType(arg);
        if (resolved == .poison) return .poison;
        args_buffer[position] = resolved;
    }

    const instance = try comp.instantiate(
        decl_index,
        args_buffer[0..view.args.len],
        check.origin(node),
    );
    if (comp.declAt(decl_index).kind == .type_alias) {
        try comp.ensure(.of(.alias, instance), check.origin(node));
        if (comp.instanceAt(instance).rows_state != .done) return .poison;
    }
    return comp.instanceType(instance);
}

/// Everything a body build carries. Blocks are contiguous runs.
pub const Builder = struct {
    instance: Pool.Instance,
    return_type: Pool.Index,
    insts: IR.InstList,
    extra: std.ArrayList(u32),
    blocks: std.ArrayList(BlockBuild),
    current: IR.Block.Index,
    locals: std.ArrayList(Local),
    scopes: std.ArrayList(Scope),
    defer_nodes: std.ArrayList(Node.Index),
    /// Active `is` facts, innermost last. Applied per branch, then cut back.
    narrows: std.ArrayList(Narrow),
    /// What conditions proved, gathered per condition, marked and restored.
    facts: std.ArrayList(Fact),
    /// Enclosing loops, innermost last.
    loops: std.ArrayList(LoopFrame),
    /// Scratch for `finishFunc`, retained across bodies.
    block_map: std.ArrayList(u32),
    frontier: std.ArrayList(u32),
    /// Loops below this are outside the `defer` being emitted.
    defer_loops_floor: u32,
    in_defer: bool,
    /// Unreachable code is still checked, then dropped.
    reachable: bool,

    const BlockBuild = struct { first: u32, count: u32, terminator: IR.Terminator };

    const Local = struct {
        name: Pool.String,
        node: Node.Index,
        kind: Kind,
        /// Reinterpreted by `kind`, the way `Node.Data` is by its tag.
        payload: Payload,
        /// A `var_slot` ref is a pointer to this.
        type: Pool.Index,

        const Kind = enum(u8) { let_constant, let_value, var_slot, param };

        /// The constant, the `var_slot` address, or the value ref, by `kind`.
        const Payload = union {
            ref: Ref,
            constant: Pool.Index,
        };

        const Index = handle.Index("local");

        comptime {
            if (std.debug.runtime_safety == false) assert(@sizeOf(Payload) == 4);
        }
    };

    const Scope = struct {
        locals_start: u32,
        defers_start: u32,
    };

    const Narrow = struct {
        local: Local.Index,
        type: Pool.Index,
        ref: Ref,
    };

    const LoopFrame = struct {
        /// `.empty` when the loop has no label.
        label: Pool.String,
        /// For the note when a label is shadowed.
        node: Node.Index,
        /// The `continue` target, which re-reads the condition.
        header: IR.Block.Index,
        /// The `break` target.
        exit: IR.Block.Index,
        /// Scopes at entry. Leaving the loop unwinds down to here.
        scope_depth: u32,
        /// What every `break` leaves behind.
        join: Join,
        /// A reachable `break` reached the exit.
        broke_reachable: bool,
    };

    pub const empty: Builder = .{
        .instance = undefined,
        .return_type = undefined,
        .insts = .empty,
        .extra = .empty,
        .blocks = .empty,
        .current = undefined,
        .locals = .empty,
        .scopes = .empty,
        .defer_nodes = .empty,
        .narrows = .empty,
        .facts = .empty,
        .loops = .empty,
        .block_map = .empty,
        .frontier = .empty,
        .defer_loops_floor = undefined,
        .in_defer = undefined,
        .reachable = undefined,
    };

    fn blockAt(builder: *Builder, index: IR.Block.Index) *BlockBuild {
        assert(index.int() < builder.blocks.items.len);
        return &builder.blocks.items[index.int()];
    }

    fn currentBlock(builder: *Builder) *BlockBuild {
        return builder.blockAt(builder.current);
    }

    fn clear(builder: *Builder) void {
        builder.insts.clearRetainingCapacity();
        builder.extra.clearRetainingCapacity();
        builder.blocks.clearRetainingCapacity();
        builder.locals.clearRetainingCapacity();
        builder.scopes.clearRetainingCapacity();
        builder.defer_nodes.clearRetainingCapacity();
        builder.narrows.clearRetainingCapacity();
        builder.facts.clearRetainingCapacity();
        builder.loops.clearRetainingCapacity();
        builder.block_map.clearRetainingCapacity();
        builder.frontier.clearRetainingCapacity();
    }

    pub fn deinit(builder: *Builder, gpa: Allocator) void {
        builder.insts.deinit(gpa);
        builder.extra.deinit(gpa);
        builder.blocks.deinit(gpa);
        builder.locals.deinit(gpa);
        builder.scopes.deinit(gpa);
        builder.defer_nodes.deinit(gpa);
        builder.narrows.deinit(gpa);
        builder.facts.deinit(gpa);
        builder.loops.deinit(gpa);
        builder.block_map.deinit(gpa);
        builder.frontier.deinit(gpa);
        builder.* = undefined;
    }
};

/// One body into a `Func`. The signature is already resolved.
pub fn fnBody(comp: *Compilation, instance: Pool.Instance) Allocator.Error!bool {
    const decl_index = comp.instanceDecl(instance);
    const decl = comp.declAt(decl_index);
    if (comp.instanceAt(instance).rows_state != .done) return false;

    var buffer: [bindings_max]Binding = undefined;
    const bindings = try bindTypeParams(comp, instance, &buffer);
    var check = context(comp, decl_index, bindings);

    const builder = &comp.body_builder;
    assert(builder.insts.len == 0);
    assert(builder.locals.items.len == 0);
    assert(builder.facts.items.len == 0);

    builder.instance = instance;
    builder.return_type = comp.instanceType(instance);
    builder.current = .entry;
    builder.defer_loops_floor = 0;
    builder.in_defer = false;
    builder.reachable = true;
    defer builder.clear();

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
    // one local per parameter, and room for the first few lets
    try builder.locals.ensureTotalCapacity(comp.gpa, rows.len + 8);
    for (rows) |row| {
        const param_ref = try check.emit(row.node, .param, row.type, .{ .name = row.name });
        try check.declareLocal(.{
            .name = row.name,
            .node = row.node,
            .kind = .param,
            .payload = .{ .ref = param_ref },
            .type = row.type,
        }, row.node);
    }

    // a body is statement position, so `return` is always written
    _ = try check.checkBlockValue(body_node, .void_type);
    if (check.blockOpen()) {
        const falls_off = builder.reachable and builder.return_type != .void_type;
        if (falls_off) {
            try check.failToken(view.name_token, .{
                .code = .missing_return,
                .message = try comp.fmt("not every path through '{s}' returns its {s}", .{
                    comp.pool.stringText(decl.name),
                    try comp.typeName(builder.return_type),
                }),
                .label = "a path falls off the end",
                .help = "every path must end in 'return', or loop forever",
            });
        }
        check.endBlock(.{ .ret = .none });
    }
    assert(builder.scopes.items.len == 0);
    // every gathering site restores what it marked, so nothing outlives the body
    assert(builder.facts.items.len == 0);

    try check.finishFunc();
    return true;
}

// blocks and instructions

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

/// Producing the slot address. `.empty` names a checker temporary.
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
    try builder.blocks.append(check.comp.gpa, .{
        .first = 0,
        .count = 0,
        .terminator = .none,
    });
    return index;
}

fn startBlock(check: *Check, block: IR.Block.Index) void {
    const builder = check.body();
    const opened = builder.blockAt(block);
    assert(opened.terminator == .none);

    opened.first = @intCast(builder.insts.len);
    builder.current = block;
}

fn endBlock(check: *Check, terminator: IR.Terminator) void {
    const builder = check.body();
    const block = builder.currentBlock();
    assert(terminator != .none);
    assert(block.terminator == .none);

    block.count = @as(u32, @intCast(builder.insts.len)) - block.first;
    block.terminator = terminator;
}

fn blockOpen(check: *const Check) bool {
    const builder = check.body();
    return builder.currentBlock().terminator == .none;
}

/// What follows a leave lands in a block nothing reaches, which `finishFunc` drops.
/// The path ends here, so what follows it belongs to another block.
pub fn trap(check: *Check) Allocator.Error!void {
    try check.reopenDead();
    check.endBlock(.trap);
}

fn reopenDead(check: *Check) Allocator.Error!void {
    const builder = check.body();
    if (builder.currentBlock().terminator == .none) return;

    const dead = try check.newBlock();
    check.startBlock(dead);
    builder.reachable = false;

    assert(check.blockOpen());
}

// scopes, locals, and every way out

fn pushScope(check: *Check) Allocator.Error!void {
    const builder = check.body();
    try builder.scopes.append(check.comp.gpa, .{
        .locals_start = @intCast(builder.locals.items.len),
        .defers_start = @intCast(builder.defer_nodes.items.len),
    });
}

fn popScope(check: *Check) void {
    const builder = check.body();
    const scope = builder.scopes.pop().?;
    builder.locals.shrinkRetainingCapacity(scope.locals_start);
    builder.defer_nodes.shrinkRetainingCapacity(scope.defers_start);
}

/// Defers in reverse, innermost scope down to `target`. Every way out goes through here.
fn unwindScopesTo(check: *Check, target: u32) Allocator.Error!void {
    const builder = check.body();
    assert(target <= builder.scopes.items.len);

    var index = builder.scopes.items.len;
    while (index > target) {
        index -= 1;
        const scope = builder.scopes.items[index];

        const defers_end = if (index + 1 < builder.scopes.items.len)
            builder.scopes.items[index + 1].defers_start
        else
            builder.defer_nodes.items.len;

        var defer_index = defers_end;
        while (defer_index > scope.defers_start) {
            defer_index -= 1;
            try check.emitDefer(builder.defer_nodes.items[defer_index]);
        }
    }
}

fn emitDefer(check: *Check, node: Node.Index) Allocator.Error!void {
    const builder = check.body();
    const outer = builder.in_defer;
    const floor = builder.defer_loops_floor;

    // a loop opened inside the defer may still be left, anything below may not
    builder.in_defer = true;
    builder.defer_loops_floor = @intCast(builder.loops.items.len);
    defer {
        builder.in_defer = outer;
        builder.defer_loops_floor = floor;
    }
    try check.checkStatement(node);
}

fn declareLocal(check: *Check, local: Builder.Local, node: Node.Index) Allocator.Error!void {
    const builder = check.body();
    const pool = &check.comp.pool;

    // locals may not shadow anything visible
    const clash: ?Compilation.Report = clash: {
        for (builder.locals.items) |other| {
            if (other.name == local.name) {
                break :clash .{
                    .code = .shadows,
                    .message = try check.comp.fmt("'{s}' is already in scope", .{
                        pool.stringText(local.name),
                    }),
                    .label = "shadows the outer one",
                    .notes = try check.comp.notes(&.{
                        check.comp.noteAt(check.module_index, other.node, "first bound here"),
                    }),
                };
            }
        }
        for (check.bindings) |binding| {
            if (binding.name == local.name) {
                break :clash .{
                    .code = .shadows,
                    .message = try check.comp.fmt("'{s}' is a type parameter here", .{
                        pool.stringText(local.name),
                    }),
                    .label = "shadows it",
                };
            }
        }
        if (Pool.isPrimitiveName(local.name)) {
            break :clash .{
                .code = .shadows,
                .message = try check.comp.fmt("'{s}' is the name of a type every file can see", .{
                    pool.stringText(local.name),
                }),
                .label = "shadows it",
            };
        }
        if (check.module.findDecl(pool.stringText(local.name))) |decl_index| {
            const decl = check.comp.declAt(decl_index);
            break :clash .{
                .code = .shadows,
                .message = try check.comp.fmt("'{s}' is already declared in this file", .{
                    pool.stringText(local.name),
                }),
                .label = "shadows it",
                .notes = try check.comp.notes(&.{
                    check.comp.noteAt(check.module_index, decl.node, "declared here"),
                }),
            };
        }
        break :clash null;
    };
    if (clash) |report| try check.fail(node, report);

    try builder.locals.append(check.comp.gpa, local);
}

fn findLocal(check: *const Check, name: []const u8) ?Builder.Local {
    const index = check.findLocalIndex(name) orelse return null;
    return check.localAt(index);
}

fn findLocalIndex(check: *const Check, name: []const u8) ?Builder.Local.Index {
    const builder = check.builder orelse return null;
    var index = builder.locals.items.len;
    while (index > 0) {
        index -= 1;
        const local = builder.locals.items[index];
        if (check.comp.pool.sameText(local.name, name)) return .from(index);
    }
    return null;
}

fn localAt(check: *const Check, index: Builder.Local.Index) Builder.Local {
    const builder = check.body();
    assert(index.int() < builder.locals.items.len);
    return builder.locals.items[index.int()];
}

fn loopAt(check: *const Check, index: usize) Builder.LoopFrame {
    const builder = check.body();
    assert(index < builder.loops.items.len);
    return builder.loops.items[index];
}

fn loopPtr(check: *Check, index: usize) *Builder.LoopFrame {
    const builder = check.body();
    assert(index < builder.loops.items.len);
    return &builder.loops.items[index];
}

fn activeNarrow(check: *const Check, local: Builder.Local.Index) ?Builder.Narrow {
    const builder = check.body();
    var index = builder.narrows.items.len;
    while (index > 0) {
        index -= 1;
        const narrow = builder.narrows.items[index];
        if (narrow.local == local) return narrow;
    }
    return null;
}

// statements

/// One block with its own scope, worth its final expression.
fn checkBlockValue(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    assert(check.tree.nodeTag(node) == .block);
    const builder = check.body();
    const statements = check.tree.viewOf(node).block;

    try check.pushScope();
    const depth: u32 = @intCast(builder.scopes.items.len - 1);
    defer check.popScope();

    const narrows_mark = builder.narrows.items.len;
    defer builder.narrows.shrinkRetainingCapacity(narrows_mark);

    var value: Value = .void_value;
    for (statements, 0..) |statement, position| {
        if (check.blockOpen() == false or builder.reachable == false) {
            // entered dead, so whatever led here already reported
            if (position > 0) {
                try check.reportUnreachable(statement, statements[position - 1]);
            }
            break;
        }
        const tail = position + 1 == statements.len;
        const is_value = tail and wantsValue(hint) and
            tagIsStatement(check.tree.nodeTag(statement)) == false;
        if (is_value) {
            value = try check.checkExpr(statement, hint);
        } else {
            try check.checkStatement(statement);
        }
    }

    if (check.blockOpen() == false) return .diverged;
    // open but unreachable completes no value either
    if (builder.reachable == false) return .diverged;
    try check.unwindScopesTo(depth);
    return value;
}

fn reportUnreachable(
    check: *Check,
    statement: Node.Index,
    left_at: Node.Index,
) Allocator.Error!void {
    try check.fail(statement, .{
        .code = .unreachable_code,
        .message = "this cannot be reached",
        .label = "never runs",
        .notes = try check.comp.notes(&.{
            check.comp.noteAt(check.module_index, left_at, "the block already left here"),
        }),
    });
}

fn checkStatement(check: *Check, node: Node.Index) Allocator.Error!void {
    assert(check.builder != null);

    switch (check.tree.viewOf(node)) {
        .var_decl => try check.checkVarDecl(node),
        .assign => |assign| try check.checkAssign(node, assign),
        .defer_stmt => |deferred| try check.checkDefer(deferred),
        .err => {},
        // a void hint tells an `if` to drop its value
        else => {
            const value = try check.checkExpr(node, .void_type);
            if (check.guardStatement(node)) |lhs| {
                const mark: u32 = @intCast(check.body().facts.items.len);
                defer check.body().facts.shrinkRetainingCapacity(mark);

                const facts = try check.gatherFacts(lhs);
                try check.applyFacts(facts.when_true);
                return;
            }
            try check.expectNothing(node, value);
        },
    }
}

/// `a or return` standing alone. What its left side settled holds for the rest.
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

    const value = try check.checkExpr(view.init_expr, annotation);

    switch (value) {
        .diverged, .poison => try check.declarePoisoned(name, node),
        .constant => {
            const met = if (annotation) |wanted|
                try check.coerce(value, wanted, view.init_expr)
            else
                value;
            switch (met) {
                .constant => |final| {
                    if (view.is_mutable) {
                        try check.checkVarDeclSlot(node, name, .{ .constant = final }, annotation);
                    } else {
                        try check.declareLocal(.{
                            .name = name,
                            .node = node,
                            .kind = .let_constant,
                            .payload = .{ .constant = final },
                            .type = comp.pool.typeOfValue(final),
                        }, node);
                    }
                },
                else => try check.checkVarDeclSlot(node, name, met, annotation),
            }
        },
        .runtime => try check.checkVarDeclSlot(node, name, value, annotation),
        else => {
            try check.reportNotValue(view.init_expr, value);
            try check.declarePoisoned(name, node);
        },
    }
}

/// Bind a runtime value. A `let` keeps the ref, a `var` gets storage.
fn checkVarDeclSlot(
    check: *Check,
    node: Node.Index,
    name: Pool.String,
    value: Value,
    annotation: ?Pool.Index,
) Allocator.Error!void {
    const comp = check.comp;
    const view = check.tree.viewOf(node).var_decl;

    var final = value;
    if (annotation) |wanted| final = try check.coerce(value, wanted, view.init_expr);

    const value_type = check.typeOf(final);
    if (value_type == .void_type) {
        try check.fail(view.init_expr, .{
            .code = .type_mismatch,
            .message = "this produces nothing, so there is nothing to bind",
            .label = "no value here",
        });
        return check.declarePoisoned(name, node);
    }
    if (value_type == .poison) return check.declarePoisoned(name, node);

    // a sealed constant carries its type here, so only an unchosen one needs words
    if (final == .constant and annotation == null and Pool.isUntyped(value_type)) {
        assert(view.is_mutable);
        const example: ?[]const u8 = switch (comp.pool.keyOf(final.constant)) {
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
                .message = try comp.fmt("'{s}' needs a type before it can vary", .{
                    comp.pool.stringText(name),
                }),
                .label = "no type to hold it",
                .help = try comp.fmt("write 'var {s}: {s} = ...', or whichever type is meant", .{
                    comp.pool.stringText(name), shape,
                }),
            });
            return check.declarePoisoned(name, node);
        }
    }

    if (view.is_mutable == false) {
        try check.declareLocal(.{
            .name = name,
            .node = node,
            .kind = .let_value,
            .payload = .{ .ref = refOf(final) },
            .type = value_type,
        }, node);
        return;
    }

    const slot = try check.emitSlot(node, name, value_type);
    try check.emitStore(node, slot, refOf(final));
    try check.declareLocal(.{
        .name = name,
        .node = node,
        .kind = .var_slot,
        .payload = .{ .ref = slot },
        .type = value_type,
    }, node);
}

/// The element type a suggested annotation names, so the suggestion is one that fits.
fn elementExample(check: *Check, aggregate: Pool.Key.Aggregate) Allocator.Error![]const u8 {
    if (aggregate.elems.len == 0) return "u32";

    const found = check.comp.pool.typeOfValue(aggregate.elems[0]);
    if (Pool.isUntyped(found)) return "u32";
    return check.comp.typeName(found);
}

fn declarePoisoned(check: *Check, name: Pool.String, node: Node.Index) Allocator.Error!void {
    try check.declareLocal(.{
        .name = name,
        .node = node,
        .kind = .let_constant,
        .payload = .{ .constant = .poison },
        .type = .poison,
    }, node);
}

fn checkAssign(check: *Check, node: Node.Index, assign: AST.View.Assign) Allocator.Error!void {
    if (assign.op == null and check.tree.nodeTag(assign.lhs) == .ident) {
        const text = check.mainTokenText(assign.lhs);
        if (Module.isDiscard(text)) return check.checkDiscard(assign.rhs);
    }

    const place = try check.checkPlace(assign.lhs) orelse {
        _ = try check.checkExpr(assign.rhs, null);
        return;
    };
    if (place.mutable == false) {
        try check.reportImmutable(assign.lhs, place);
        _ = try check.checkExpr(assign.rhs, place.type);
        return;
    }
    assert(place.kind == .address);
    if (place.type == .poison) return;

    const value: Value = if (assign.op) |op| folded: {
        // the place is read once, worked on, and written back
        const held = try check.placeValue(place);
        const rhs = try check.checkExpr(assign.rhs, place.type);
        if (rhs == .diverged) return;
        if (try check.valueOnly(assign.rhs, rhs) == false) return;

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

/// `_ = e` drops a value on purpose.
fn checkDiscard(check: *Check, rhs: Node.Index) Allocator.Error!void {
    const value = try check.checkExpr(rhs, null);
    _ = try check.valueOnly(rhs, value);
}

fn checkIf(
    check: *Check,
    node: Node.Index,
    view: AST.View.If,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const builder = check.body();
    const entry_reachable = builder.reachable;

    const wants = wantsValue(hint);
    if (wants and view.else_node == .none) {
        try check.fail(node, .{
            .code = .type_mismatch,
            .message = "this 'if' has no 'else', so one path through it produces nothing",
            .label = "needs an 'else'",
            .help = "an 'if' used as a value says what it is on every path",
        });
    }
    const carries = wants and view.else_node != .none;
    // neither arm is more responsible for the type than the other, so the whole `if` names it
    var join = try Join.open(check, "if", node, carries, hint, node.toOptional());

    const then_block = try check.newBlock();
    const else_block = try check.newBlock();
    const join_block = try check.newBlock();

    const cond = try check.checkCondition(view.cond);

    const facts_mark: u32 = @intCast(builder.facts.items.len);
    defer builder.facts.shrinkRetainingCapacity(facts_mark);

    const facts = try check.gatherFacts(view.cond);

    try check.reopenDead();
    check.endBlock(.{ .branch = .{
        .cond = cond,
        .then_block = then_block,
        .else_block = else_block,
    } });

    const narrows_mark = builder.narrows.items.len;

    check.startBlock(then_block);
    try check.applyFacts(facts.when_true);
    const then_value = try check.checkExpr(view.then_block, hint);
    builder.narrows.shrinkRetainingCapacity(narrows_mark);
    try join.take(check, then_value, view.then_block);

    var join_reachable = check.blockOpen() and builder.reachable;
    if (check.blockOpen()) check.endBlock(.{ .jump = join_block });

    check.startBlock(else_block);
    builder.reachable = entry_reachable;
    var else_value: Value = .diverged;
    if (view.else_node.unwrap()) |else_node| {
        try check.applyFacts(facts.when_false);

        else_value = try check.checkExpr(else_node, hint);

        builder.narrows.shrinkRetainingCapacity(narrows_mark);
        try join.take(check, else_value, else_node);

        if (check.blockOpen() and builder.reachable) join_reachable = true;
        if (check.blockOpen()) check.endBlock(.{ .jump = join_block });
    } else {
        if (entry_reachable) join_reachable = true;
        check.endBlock(.{ .jump = join_block });
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    // one door into the join leaves its proof standing past the `if`
    if (then_value == .diverged and (view.else_node == .none or else_value != .diverged)) {
        try check.applyFacts(facts.when_false);
    }
    if (then_value != .diverged and view.else_node != .none and else_value == .diverged) {
        try check.applyFacts(facts.when_true);
    }

    return join.close(check, then_value == .diverged and else_value == .diverged);
}

/// Where the arms of an `if`, a loop, or a `match` leave their value. The first
/// arm that does not leave names the type, and every arm after meets it.
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

    /// What an arm's body is checked against.
    fn armHint(join: Join) ?Pool.Index {
        if (join.carries == false) return .void_type;
        return if (join.settled) join.result_type else null;
    }

    fn take(join: *Join, check: *Check, value: Value, at: Node.Index) Allocator.Error!void {
        if (join.carries == false) return;
        if (value == .diverged) return;

        if (join.settled == false) {
            const blamed = join.names_type.unwrap() orelse at;
            join.result_type = try check.settleType(blamed, check.typeOf(value), join.what);
            join.settled = true;
        }
        const met = try check.coerce(value, join.result_type, at);
        try check.emitStore(at, join.slot, refOf(met));
    }

    /// What the arms left behind. A later stage reads every type, so the slot is
    /// typed whether or not the value is read.
    fn close(join: Join, check: *Check, diverged: bool) Allocator.Error!Value {
        if (join.carries == false) return .void_value;
        try check.setSlotType(join.slot, join.result_type);

        if (diverged) return .diverged;
        if (join.result_type == .poison) return .poison;
        const loaded = try check.emitOne(join.node, .load, join.result_type, join.slot);
        return runtimeValue(loaded, join.result_type);
    }
};

/// The type a branch settled on, or poison once reported. `what` is the keyword.
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
        return .poison;
    }
    try check.fail(node, .{
        .code = .var_needs_type,
        .message = try comp.fmt("nothing says what type this '{s}' is", .{what}),
        .label = "no type in sight",
        .help = try comp.fmt("annotate what it feeds, as in 'let n: i64 = {s} ...'", .{what}),
    });
    return .poison;
}

/// The name an exit reaches this loop by, which no enclosing loop may share.
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
            .notes = try comp.notes(&.{
                comp.noteAt(check.module_index, other.node, "first labeled here"),
            }),
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

    // control may have left already, the way `emit` handles it
    try check.reopenDead();
    const entry_reachable = builder.reachable;

    const carries = wantsValue(hint);

    // a loop that can end on its own needs `else` to say what it is then
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

    const header = try check.newBlock();
    const body_block = try check.newBlock();
    const exit = try check.newBlock();
    const else_target: IR.Block.Index = if (view.else_node != .none)
        try check.newBlock()
    else
        exit;
    // the increment stands apart, so `continue` reaches it before the test
    const latch: IR.Block.Index = if (counter != null) try check.newBlock() else header;

    check.endBlock(.{ .jump = header });
    check.startBlock(header);
    // the header never narrows, so no facts are gathered here
    const holds: ?Ref = switch (view.head) {
        .forever => null,
        .cond => |cond_node| asked: {
            const cond = try check.checkCondition(cond_node);
            try check.reopenDead();
            break :asked cond;
        },
        .range => try check.counterBelowEnd(counter),
    };
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
    builder.reachable = entry_reachable;
    if (counting) |it| try check.bindCounter(it.name, counter);
    _ = try check.checkBlockValue(view.body, .void_type);
    if (counting != null) check.popScope();
    if (check.blockOpen()) check.endBlock(.{ .jump = latch });

    if (counter) |it| {
        check.startBlock(latch);
        try check.countOn(it);
        check.endBlock(.{ .jump = header });
    }

    const finished = builder.loops.pop().?;
    join = finished.join;

    var else_flows = false;
    if (view.else_node.unwrap()) |else_node| {
        check.startBlock(else_target);
        if (view.head.ends() == false) {
            builder.reachable = false;
            try check.fail(else_node, .{
                .code = .unreachable_code,
                .message = "this 'else' never runs, because a loop with no " ++
                    "condition never ends on its own",
                .label = "never runs",
            });
        } else {
            builder.reachable = entry_reachable;
        }

        const else_value = try check.checkExpr(else_node, join.armHint());
        try join.take(check, else_value, else_node);
        else_flows = check.blockOpen() and builder.reachable;
        if (check.blockOpen()) check.endBlock(.{ .jump = exit });
    }

    check.startBlock(exit);
    var exit_reachable = finished.broke_reachable;
    if (view.head.ends()) {
        if (view.else_node == .none) {
            if (entry_reachable) exit_reachable = true;
        } else {
            if (else_flows) exit_reachable = true;
        }
    }
    builder.reachable = exit_reachable;

    const value = try join.close(check, exit_reachable == false);
    return if (else_missing) .poison else value;
}

/// A range loop's counter, which the header tests and the latch counts on.
const Counter = struct {
    slot: Ref,
    /// Read once, before the first pass.
    end: Ref,
    type: Pool.Index,
    node: Node.Index,
};

/// The slot a pass counts, filled with the first value. Null once reported.
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

/// The compiler's own test, typed void, so no `bool` is asked of the file.
fn counterBelowEnd(check: *Check, counter: ?Counter) Allocator.Error!Ref {
    const it = counter orelse return .fromConstant(.poison);
    const current = try check.emitOne(it.node, .load, it.type, it.slot);
    return check.emit(it.node, .cmp_lt, .void_type, .{
        .bin = .{ .lhs = current, .rhs = it.end },
    });
}

/// The name a pass binds, which is a `let`, so the body cannot move it.
fn bindCounter(check: *Check, name: Node.Index, counter: ?Counter) Allocator.Error!void {
    try check.pushScope();

    const text = check.mainTokenText(name);
    if (Module.isDiscard(text)) return check.failDiscard(name);
    const named = try check.comp.pool.string(check.comp.gpa, text);

    const it = counter orelse return check.declarePoisoned(named, name);
    const current = try check.emitOne(name, .load, it.type, it.slot);
    try check.declareLocal(.{
        .name = named,
        .node = name,
        .kind = .let_value,
        .payload = .{ .ref = current },
        .type = it.type,
    }, name);
}

/// One step, which cannot overflow, because the test proved the counter below the end.
fn countOn(check: *Check, counter: Counter) Allocator.Error!void {
    const comp = check.comp;
    const current = try check.emitOne(counter.node, .load, counter.type, counter.slot);
    const one = try comp.pool.intern(comp.gpa, .{
        .value_int = .{ .type = counter.type, .value = 1 },
    });
    const next = try check.emit(counter.node, .add, counter.type, .{
        .bin = .{ .lhs = current, .rhs = .fromConstant(one) },
    });
    try check.emitStore(counter.node, counter.slot, next);
}

/// A slot exists before its arms have said what type it is.
fn setSlotType(check: *Check, slot: Ref, value_type: Pool.Index) Allocator.Error!void {
    const builder = check.body();
    const index = switch (slot.unwrap()) {
        .inst => |inst| inst.int(),
        .constant => unreachable,
    };
    assert(builder.insts.items(.tag)[index] == .local);
    builder.insts.items(.type)[index] = try check.pointerTo(value_type, true);
}

// match, the n-way `is`

const Arm = handle.Index("match arm");

/// Which arm covered a member, `.none` until one does.
const ArmIndex = Arm.Optional;

/// Arms label members, the scrutinee narrows per arm, and coverage is counted.
fn checkMatch(
    check: *Check,
    node: Node.Index,
    view: AST.View.Match,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    const builder = check.body();
    assert(check.tree.nodeTag(node) == .match_expr);

    const entry_reachable = builder.reachable;
    const scrutinee = try check.checkExpr(view.scrutinee, null);
    try check.reopenDead();

    // a broken scrutinee poisons quietly, and the arms are still checked
    var scrutinee_type: Pool.Index = .poison;
    if (try check.valueOnly(view.scrutinee, scrutinee)) {
        const found = check.typeOf(scrutinee);
        if (comp.pool.isUnion(found)) {
            scrutinee_type = found;
        } else if (found != .poison) {
            const asks = "'match' asks which member a union holds";
            try check.failNotUnion(view.scrutinee, found, asks);
        }
    }
    const broken = scrutinee_type == .poison;

    // members are read by position, because resolving a label can intern
    const member_count: u32 = if (broken) 0 else comp.pool.unionMemberCount(scrutinee_type);
    assert(member_count <= Pool.union_members_max);
    var covered_by: [Pool.union_members_max]ArmIndex = @splat(.none);
    const covered = covered_by[0..member_count];

    // a let or parameter narrows per arm, exactly as `is` narrows it
    const narrow_local: ?Builder.Local.Index = local: {
        if (broken) break :local null;
        if (check.tree.nodeTag(view.scrutinee) != .ident) break :local null;
        const text = check.mainTokenText(view.scrutinee);
        const index = check.findLocalIndex(text) orelse break :local null;
        switch (check.localAt(index).kind) {
            .let_value, .param => break :local index,
            .let_constant, .var_slot => break :local null,
        }
    };

    // exhaustiveness spares the last arm its test, so it is the fall-through door
    const fallthrough: usize = last: {
        var index = view.arms.len;
        while (index > 0) {
            index -= 1;
            if (check.tree.nodeTag(view.arms[index]) == .match_arm) break :last index;
        }
        // recovery already reported whatever left holes behind
        if (view.arms.len == 0 and broken == false) {
            _ = try check.checkMatchMissing(node, scrutinee_type, covered);
        }
        return .poison;
    };

    var join = try Join.open(check, "match", node, wantsValue(hint), hint, .none);
    const join_block = try check.newBlock();

    var join_reachable = false;
    var all_diverged = true;
    // narrowing past the match needs the whole picture to have been proven
    var coverage_clean = broken == false;
    var survivors: [Pool.union_members_max]bool = @splat(false);
    const narrows_mark = builder.narrows.items.len;

    for (view.arms, 0..) |arm_node, arm_raw| {
        if (check.tree.nodeTag(arm_node) != .match_arm) {
            // a hole from recovery could have covered anything
            coverage_clean = false;
            continue;
        }
        const arm_index = Arm.from(arm_raw).toOptional();
        const arm = check.tree.viewOf(arm_node).match_arm;

        var arm_type: Pool.Index = .poison;
        if (arm.label.unwrap()) |label_node| {
            arm_type = try check.resolveType(label_node);
            if (arm_type != .poison and broken == false) {
                arm_type = try check.checkMatchCover(
                    label_node,
                    arm_type,
                    scrutinee_type,
                    covered,
                    arm_index,
                    view.arms,
                );
            }
        } else if (broken == false) {
            arm_type = try check.checkMatchRest(arm_node, scrutinee_type, covered, arm_index);
        }
        if (arm_type == .poison) coverage_clean = false;

        const arm_block = try check.newBlock();
        var resume_chain: ?IR.Block.Index = null;
        if (arm_raw == fallthrough) {
            check.endBlock(.{ .jump = arm_block });
        } else {
            try check.checkMatchTests(
                arm_node,
                scrutinee_type,
                refOf(scrutinee),
                covered,
                arm_index,
                arm_block,
            );
            resume_chain = builder.current;
        }

        check.startBlock(arm_block);
        builder.reachable = entry_reachable;
        if (narrow_local) |local| {
            if (arm_type != .poison) {
                try check.applyFact(.{ .local = local, .type = arm_type, .node = arm_node });
            }
        }

        const arm_value = try check.checkExpr(arm.body, join.armHint());
        builder.narrows.shrinkRetainingCapacity(narrows_mark);

        if (arm_value != .diverged) {
            all_diverged = false;
            try join.take(check, arm_value, arm.body);
            if (join.carries == false) try check.expectNothing(arm.body, arm_value);
        }

        if (check.blockOpen()) {
            if (builder.reachable) {
                join_reachable = true;
                for (covered, 0..) |cover, position| {
                    if (cover == arm_index) survivors[position] = true;
                }
            }
            check.endBlock(.{ .jump = join_block });
        }

        // the chain block's run restarts past the arm's instructions
        if (resume_chain) |chain| check.startBlock(chain);
    }

    // only a clean count can prove something was left out
    if (coverage_clean) {
        const left_out = try check.checkMatchMissing(node, scrutinee_type, covered);
        if (left_out) coverage_clean = false;
    }

    check.startBlock(join_block);
    builder.reachable = join_reachable;

    // arms that leave narrow what follows, the way a branch that leaves does
    if (narrow_local) |local| {
        if (coverage_clean and join_reachable) {
            var rest: [Pool.union_members_max]Pool.Index = undefined;
            var count: u32 = 0;
            for (survivors[0..member_count], 0..) |survived, position| {
                if (survived == false) continue;
                rest[count] = comp.pool.unionMemberAt(scrutinee_type, @intCast(position));
                count += 1;
            }
            assert(count > 0);
            if (count < member_count) {
                const narrowed = try check.uniteRest(rest[0..count]);
                try check.applyFact(.{ .local = local, .type = narrowed, .node = node });
            }
        }
    }

    const value = try join.close(check, all_diverged);
    return if (join.carries and broken) .poison else value;
}

/// Marks what the label covers, reports repeats and strays. Poison once anything misfired.
fn checkMatchCover(
    check: *Check,
    label_node: Node.Index,
    arm_type: Pool.Index,
    scrutinee_type: Pool.Index,
    covered_by: []ArmIndex,
    arm_index: ArmIndex,
    arms: []const Node.Index,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    assert(arm_type != .poison);
    assert(covered_by.len == comp.pool.unionMemberCount(scrutinee_type));

    var clean = true;
    const multi = comp.pool.isUnion(arm_type);
    const count: u32 = if (multi) comp.pool.unionMemberCount(arm_type) else 1;
    var at: u32 = 0;
    while (at < count) : (at += 1) {
        const member = if (multi) comp.pool.unionMemberAt(arm_type, at) else arm_type;

        const position = comp.pool.unionMemberPosition(scrutinee_type, member) orelse {
            try check.failNotMember(label_node, member, scrutinee_type);
            clean = false;
            continue;
        };
        if (covered_by[position].unwrap()) |earlier| {
            // one report per arm, however many members repeat
            const first = arms[earlier.int()];
            const first_label = check.tree.viewOf(first).match_arm.label;
            try check.fail(label_node, .{
                .code = .duplicate_arm,
                .message = try comp.fmt("'{s}' is already handled by an earlier arm", .{
                    try comp.typeName(member),
                }),
                .label = "handled again here",
                .notes = try comp.notes(&.{check.comp.noteAt(
                    check.module_index,
                    first_label.unwrap() orelse first,
                    "handled here",
                )}),
            });
            clean = false;
            continue;
        }
        covered_by[position] = arm_index;
    }
    return if (clean) arm_type else .poison;
}

/// The uncovered members become the `else` arm's type. Poison when nothing is left.
fn checkMatchRest(
    check: *Check,
    arm_node: Node.Index,
    scrutinee_type: Pool.Index,
    covered_by: []ArmIndex,
    arm_index: ArmIndex,
) Allocator.Error!Pool.Index {
    const comp = check.comp;
    assert(covered_by.len == comp.pool.unionMemberCount(scrutinee_type));
    assert(covered_by.len >= 2);

    var rest: [Pool.union_members_max]Pool.Index = undefined;
    var count: u32 = 0;
    for (covered_by, 0..) |cover, position| {
        if (cover != .none) continue;
        rest[count] = comp.pool.unionMemberAt(scrutinee_type, @intCast(position));
        covered_by[position] = arm_index;
        count += 1;
    }
    if (count > 0) return check.uniteRest(rest[0..count]);

    try check.fail(arm_node, .{
        .code = .duplicate_arm,
        .message = "every member is already handled, so 'else' can never run",
        .label = "nothing left for it",
    });
    return .poison;
}

/// One member stands bare, several stay a union in the given order.
fn uniteRest(check: *Check, members: []const Pool.Index) Allocator.Error!Pool.Index {
    assert(members.len > 0);
    assert(members.len <= Pool.union_members_max);
    if (members.len == 1) return members[0];
    return check.comp.pool.intern(check.comp.gpa, .{ .type_union = members });
}

/// One test per member the arm covers. Covering nothing skips the arm whole.
fn checkMatchTests(
    check: *Check,
    node: Node.Index,
    scrutinee_type: Pool.Index,
    scrutinee_ref: Ref,
    covered_by: []const ArmIndex,
    arm_index: ArmIndex,
    arm_block: IR.Block.Index,
) Allocator.Error!void {
    assert(scrutinee_ref != .none);
    assert(check.blockOpen());

    var tested = false;
    for (covered_by, 0..) |cover, position| {
        if (cover != arm_index) continue;
        const member = check.comp.pool.unionMemberAt(scrutinee_type, @intCast(position));

        const chain = try check.newBlock();
        // the compiler's own test, typed void, so no 'bool' is asked of the file
        const held = try check.emit(node, .union_is, .void_type, .{
            .probe = .{ .operand = scrutinee_ref, .member = member },
        });
        check.endBlock(.{ .branch = .{
            .cond = held,
            .then_block = arm_block,
            .else_block = chain,
        } });
        check.startBlock(chain);
        tested = true;
    }

    if (tested == false) {
        const chain = try check.newBlock();
        check.endBlock(.{ .jump = chain });
        check.startBlock(chain);
    }
    assert(check.blockOpen());
}

/// The members no arm handles, all named at the keyword. Whether any were.
fn checkMatchMissing(
    check: *Check,
    node: Node.Index,
    scrutinee_type: Pool.Index,
    covered_by: []const ArmIndex,
) Allocator.Error!bool {
    const comp = check.comp;
    assert(covered_by.len == comp.pool.unionMemberCount(scrutinee_type));

    // named up to a cap, so a wide union does not flood the message
    const named_max = 5;
    var missing_count: u32 = 0;
    var names: ?[]const u8 = null;
    for (covered_by, 0..) |cover, position| {
        if (cover != .none) continue;
        missing_count += 1;
        if (missing_count > named_max) continue;

        const member = comp.pool.unionMemberAt(scrutinee_type, @intCast(position));
        names = try quotedList(comp, names, try comp.typeName(member));
    }
    if (missing_count == 0) return false;

    const message = if (missing_count > named_max)
        try comp.fmt("this match leaves out {s}, and {d} more members", .{
            names.?,
            missing_count - named_max,
        })
    else
        try comp.fmt("this match leaves out {s}", .{names.?});
    try check.failToken(check.tree.nodeMainToken(node), .{
        .code = .missing_arm,
        .message = message,
        .label = "not every member is handled",
        .help = "add an arm per member, or 'else =>' for the rest",
    });
    return true;
}

// narrowing, the facts a condition proves

const Fact = struct { local: Builder.Local.Index, type: Pool.Index, node: Node.Index };

/// What a condition proves about locals, per edge. Both are runs in `Builder.facts`.
const Facts = struct {
    when_true: Compilation.Range,
    when_false: Compilation.Range,

    const nothing: Facts = .{ .when_true = .empty, .when_false = .empty };
};

/// `is` proves a member when true, the rest when false. A failed `and` proves nothing.
fn gatherFacts(check: *Check, node: Node.Index) Allocator.Error!Facts {
    const builder = check.body();
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            // marked after the call, which can grow the list under a mark taken first
            const found = try check.factsOfIs(node) orelse return .nothing;
            const start: u32 = @intCast(builder.facts.items.len);
            try builder.facts.append(check.comp.gpa, found.when_true);
            try builder.facts.append(check.comp.gpa, found.when_false);
            return .{
                .when_true = .{ .start = start, .len = 1 },
                .when_false = .{ .start = start + 1, .len = 1 },
            };
        },
        .binary => |it| {
            if (it.op != .bool_and) return .nothing;
            return .{ .when_true = try check.gatherSpine(node), .when_false = .empty };
        },
        else => return .nothing,
    }
}

/// What an `and`-spine proves when the whole condition passes.
fn gatherSpine(check: *Check, node: Node.Index) Allocator.Error!Compilation.Range {
    const builder = check.body();
    const start: u32 = @intCast(builder.facts.items.len);
    try check.gatherWhenTrue(node);
    return .{ .start = start, .len = @intCast(builder.facts.items.len - start) };
}

fn gatherWhenTrue(check: *Check, node: Node.Index) Allocator.Error!void {
    switch (check.tree.viewOf(node)) {
        .is_expr => {
            const found = try check.factsOfIs(node) orelse return;
            try check.body().facts.append(check.comp.gpa, found.when_true);
        },
        .binary => |it| {
            if (it.op != .bool_and) return;
            try check.gatherWhenTrue(it.lhs);
            try check.gatherWhenTrue(it.rhs);
        },
        else => {},
    }
}

/// The member when it holds and the rest when it does not, swapped for `is not`.
fn factsOfIs(
    check: *Check,
    node: Node.Index,
) Allocator.Error!?struct { when_true: Fact, when_false: Fact } {
    const comp = check.comp;
    const view = check.tree.viewOf(node).is_expr;

    if (check.tree.nodeTag(view.operand) != .ident) return null;
    const text = check.mainTokenText(view.operand);
    const index = check.findLocalIndex(text) orelse return null;

    const local = check.localAt(index);
    switch (local.kind) {
        .let_value, .param => {},
        .let_constant, .var_slot => return null,
    }

    const found = if (check.activeNarrow(index)) |narrow| narrow.type else local.type;
    if (comp.pool.isUnion(found) == false) return null;

    const member = try check.resolveType(view.type_expr);
    if (comp.pool.unionHas(found, member) == false) return null;
    const rest = try comp.pool.unionWithout(comp.gpa, found, member);

    if (view.negated) {
        return .{
            .when_true = .{ .local = index, .type = rest, .node = node },
            .when_false = .{ .local = index, .type = member, .node = node },
        };
    }
    return .{
        .when_true = .{ .local = index, .type = member, .node = node },
        .when_false = .{ .local = index, .type = rest, .node = node },
    };
}

fn applyFacts(check: *Check, range: Compilation.Range) Allocator.Error!void {
    var at = range.start;
    // by index, because the run belongs to the builder rather than to this call
    while (at < range.end()) : (at += 1) try check.applyFact(check.body().facts.items[at]);
}

fn applyFact(check: *Check, fact: Fact) Allocator.Error!void {
    const builder = check.body();
    const local = check.localAt(fact.local);
    const source: Ref = if (check.activeNarrow(fact.local)) |narrow|
        narrow.ref
    else
        local.payload.ref;
    const narrowed = try check.emitOne(fact.node, .union_narrow, fact.type, source);
    try builder.narrows.append(check.comp.gpa, .{
        .local = fact.local,
        .type = fact.type,
        .ref = narrowed,
    });
}

fn checkIs(check: *Check, node: Node.Index, view: AST.View.Is) Allocator.Error!Value {
    const comp = check.comp;
    const operand = try check.checkExpr(view.operand, null);
    const member = try check.resolveType(view.type_expr);

    if (operand == .diverged) return .diverged;
    if (operand == .poison) return .poison;
    if (member == .poison) return .poison;
    if (try check.valueOnly(view.operand, operand) == false) return .poison;

    const found = check.typeOf(operand);
    if (found == .poison) return .poison;
    if (comp.pool.isUnion(found) == false) {
        try check.failNotUnion(node, found, "'is' asks which member a union holds");
        return .poison;
    }
    if (comp.pool.unionHas(found, member) == false) {
        try check.failNotMember(view.type_expr, member, found);
        return .poison;
    }

    assert(operand == .runtime);
    const bools = try check.boolType(node);
    const tested = try check.emit(node, .union_is, bools, .{
        .probe = .{ .operand = refOf(operand), .member = member },
    });
    if (view.negated) {
        const flipped = try check.emitOne(node, .not, bools, tested);
        return runtimeValue(flipped, bools);
    }
    return runtimeValue(tested, bools);
}

/// Two unit members, the first meaning yes. `bool` is declared, never built in.
fn boolType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = check.comp;
    if (check.bool_type != .poison) return check.bool_type;

    const shaped: Pool.Index = shaped: {
        const decl_index = check.visibleDecl(Module.bool_name) orelse break :shaped .poison;
        const found = try check.declAsType(decl_index, node);
        if (comp.pool.isUnion(found) == false) break :shaped .poison;
        if (comp.pool.unionMemberCount(found) != 2) break :shaped .poison;
        if (comp.pool.keyOf(comp.pool.unionMemberAt(found, 0)) != .type_unit) break :shaped .poison;
        if (comp.pool.keyOf(comp.pool.unionMemberAt(found, 1)) != .type_unit) break :shaped .poison;
        break :shaped found;
    };
    if (shaped == .poison) {
        // failure stays unmemoized, so every site that needs `bool` reports
        try check.fail(node, .{
            .code = .no_prelude_type,
            .message = "this needs 'bool', a union of two unit types",
            .label = "no such 'bool' in scope",
            .help = "declare 'type true', 'type false', and 'type bool = true | false'",
        });
    }
    check.bool_type = shaped;
    return shaped;
}

/// The absent member of an optional. `none` is declared, never built in.
pub fn noneType(check: *Check, node: Node.Index) Allocator.Error!Pool.Index {
    const comp = check.comp;
    if (check.none_type != .poison) return check.none_type;

    const shaped: Pool.Index = shaped: {
        const decl_index = check.visibleDecl(Module.none_name) orelse break :shaped .poison;
        const found = try check.declAsType(decl_index, node);
        if (comp.pool.keyOf(found) != .type_unit) break :shaped .poison;
        break :shaped found;
    };
    if (shaped == .poison) {
        try check.fail(node, .{
            .code = .no_prelude_type,
            .message = "this needs 'none', a unit type",
            .label = "no such 'none' in scope",
            .help = "declare 'type none'",
        });
    }
    check.none_type = shaped;
    return shaped;
}

fn truthOf(check: *const Check, bools: Pool.Index, constant: Pool.Index) ?bool {
    if (bools == .poison) return null;
    const pool = &check.comp.pool;
    const held = switch (pool.keyOf(constant)) {
        .value_union => |it| it.value,
        else => constant,
    };
    const found = pool.typeOfValue(held);
    if (found == pool.unionMemberAt(bools, 0)) return true;
    if (found == pool.unionMemberAt(bools, 1)) return false;
    return null;
}

fn truthValue(check: *Check, bools: Pool.Index, truth: bool) Allocator.Error!Pool.Index {
    if (bools == .poison) return .poison;
    const pool = &check.comp.pool;
    const member = pool.unionMemberAt(bools, if (truth) 0 else 1);
    const held = try pool.intern(check.comp.gpa, .{ .value_unit = member });
    return pool.intern(check.comp.gpa, .{ .value_union = .{ .type = bools, .value = held } });
}

/// A condition is a union, and asks whether it holds its first member.
fn checkCondition(check: *Check, node: Node.Index) Allocator.Error!Ref {
    const value = try check.checkExpr(node, null);
    const found = check.typeOf(value);
    if (found == .poison) return .fromConstant(.poison);
    if (check.comp.pool.isUnion(found)) return refOf(value);

    try check.fail(node, .{
        .code = .not_a_union,
        .message = try check.comp.fmt("this condition is {s}, and a condition is a union", .{
            try check.comp.typeName(found),
        }),
        .label = "cannot answer",
        .help = "a condition asks whether a union holds its first member",
    });
    return .fromConstant(.poison);
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
        // the operand may have left, and a block cannot be left twice
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

/// The value meets the loop's type, defers unwind to the loop, control jumps to the exit.
fn checkBreak(check: *Check, node: Node.Index, view: AST.View.Break) Allocator.Error!Value {
    const builder = check.body();

    const found = try check.findLoop(view.label);
    if (try check.exitLeavesDefer(node, found)) return .poison;
    const frame_index = found orelse {
        if (view.value.unwrap()) |value_node| _ = try check.checkExpr(value_node, null);
        return check.reportNoLoop(node, view.label);
    };
    const frame = check.loopAt(frame_index);

    if (view.value.unwrap()) |value_node| {
        if (frame.join.carries) {
            const value = try check.checkExpr(value_node, frame.join.armHint());
            // the value may have left, and a block cannot be left twice
            if (check.blockOpen() == false) return .diverged;

            // checking the value can settle the loop, so reach the frame fresh
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
    const found = try check.findLoop(label);
    if (try check.exitLeavesDefer(node, found)) return .poison;
    const frame_index = found orelse return check.reportNoLoop(node, label);

    const frame = check.loopAt(frame_index);
    try check.unwindScopesTo(frame.scope_depth);
    check.endBlock(.{ .jump = frame.header });
    return .diverged;
}

/// Whether this exit would leave the `defer` it stands in. Reported.
fn exitLeavesDefer(check: *Check, node: Node.Index, found: ?usize) Allocator.Error!bool {
    const builder = check.body();
    if (builder.in_defer == false) return false;
    if (found != null and found.? >= builder.defer_loops_floor) return false;

    try check.failDeferLeaves(node, "not allowed here");
    return true;
}

fn failDeferLeaves(check: *Check, node: Node.Index, label: []const u8) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .defer_cannot_leave,
        .message = "a 'defer' runs on the way out, so it cannot leave again",
        .label = label,
    });
}

/// The innermost enclosing loop, or the one the label names. Reports nothing.
fn findLoop(check: *Check, label: ?Token.Index) Allocator.Error!?usize {
    const count = check.body().loops.items.len;

    const token = label orelse {
        if (count == 0) return null;
        return count - 1;
    };
    const name = try check.comp.pool.string(check.comp.gpa, check.tree.tokenSlice(token));
    var index = count;
    while (index > 0) {
        index -= 1;
        if (check.loopAt(index).label == name) return index;
    }
    return null;
}

fn reportNoLoop(check: *Check, node: Node.Index, label: ?Token.Index) Allocator.Error!Value {
    if (label) |token| {
        try check.fail(node, .{
            .code = .outside_loop,
            .message = try check.comp.fmt("no enclosing loop is labeled ':{s}'", .{
                check.tree.tokenSlice(token),
            }),
            .label = "no such loop",
        });
        return .poison;
    }
    try check.fail(node, .{
        .code = .outside_loop,
        .message = "there is no loop here to leave",
        .label = "outside every loop",
    });
    return .poison;
}

fn checkDefer(check: *Check, deferred: Node.Index) Allocator.Error!void {
    try check.body().defer_nodes.append(check.comp.gpa, deferred);
}

/// A statement expression must amount to nothing.
fn expectNothing(check: *Check, node: Node.Index, value: Value) Allocator.Error!void {
    switch (value) {
        .poison, .diverged => return,
        .constant, .runtime => {},
        else => return check.reportNotValue(node, value),
    }

    const found = check.typeOf(value);
    if (found == .void_type) return;
    if (found == .poison) return;

    try check.reportUnusedValue(node, found, "bind it, return it, or drop it with '_ ='");
}

/// A constant that has not met a type has no name to print.
fn reportUnusedValue(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    help: []const u8,
) Allocator.Error!void {
    const named = check.typeCanHold(found);
    try check.fail(node, .{
        .code = .value_unused,
        .message = if (named)
            try check.comp.fmt("this {s} goes nowhere", .{try check.comp.typeName(found)})
        else
            "this value goes nowhere",
        .label = "unused value",
        .help = help,
    });
}

// expressions

pub fn checkExpr(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const value = try check.checkExprInner(node, hint);
    if (check.comp.record_expr_types) try check.checkExprRemember(node, value);
    return value;
}

/// The editor's record, so the IR is one consumer of the answer rather than the only copy.
fn checkExprRemember(check: *Check, node: Node.Index, value: Value) Allocator.Error!void {
    assert(check.comp.record_expr_types);
    const builder = check.builder orelse return;

    switch (value) {
        .constant, .runtime => {},
        else => return,
    }
    const found = check.typeOf(value);
    if (found == .poison) return;
    try check.comp.rememberExprType(builder.instance, node, found);
}

fn checkExprInner(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    // a top-level binding has no body to lower into
    if (check.builder == null) {
        if (runtimeOnly(check.tree.nodeTag(node))) |what| return check.needRuntime(node, what);
    }

    switch (check.tree.viewOf(node)) {
        // a builtin is reached only by calling it, which `resolveCallee` answers
        .builtin => return Builtin.notAValue(check, node),
        .ident => return check.checkIdent(node),
        .number_literal => return check.checkNumber(node),
        .string_literal => return check.checkString(node),
        .char_literal => return check.checkChar(node),
        // a block reaches here as an arm
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
        .err => return .poison,
        // the parser keeps statements out of expression position
        else => unreachable,
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
        switch (local.kind) {
            .let_constant => return .{ .constant = local.payload.constant },
            .let_value, .param => {
                if (check.activeNarrow(index)) |narrow| {
                    return runtimeValue(narrow.ref, narrow.type);
                }
                return runtimeValue(local.payload.ref, local.type);
            },
            .var_slot => {
                const loaded = try check.emitOne(node, .load, local.type, local.payload.ref);
                return runtimeValue(loaded, local.type);
            },
        }
    }

    for (check.bindings) |binding| {
        if (comp.pool.sameText(binding.name, text)) return .{ .named_type = binding.type };
    }

    if (Pool.primitiveType(text)) |primitive| return .{ .named_type = primitive };

    if (check.visibleDecl(text)) |decl_index| {
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
        // the declaration settles the gate and the shape, so ask it first
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
        // a unit type in a value position is its one value
        .unit_decl => {
            const unit_type = try comp.pool.intern(comp.gpa, .{ .type_unit = decl_index });
            const value = try comp.pool.intern(comp.gpa, .{ .value_unit = unit_type });
            return .{ .constant = value };
        },
        .import => {
            if (try check.ensured(decl_index, node) == null) return .poison;
            switch (Module.importTarget(comp, decl_index)) {
                .module => |target| return .{ .named_module = target },
                .decl => |target| return check.declAsValue(target, node),
            }
        },
    }
}

fn checkNumber(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;
    const text = check.mainTokenText(node);

    switch (try number.decode(comp.arena.allocator(), text)) {
        .int => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_int = .{ .type = .untyped_int_type, .value = value },
        }) },
        .float => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_float = .{ .type = .untyped_float_type, .value = value },
        }) },
        .refused => |refusal| {
            try check.failRefusal(node, refusal);
            return .poison;
        },
    }
}

fn checkString(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;

    const mark = comp.pool.scratch.items.len;
    defer comp.pool.scratch.shrinkRetainingCapacity(mark);

    var reading = literal.bytesOf(check.mainTokenText(node));
    while (reading.next()) |piece| switch (piece) {
        // bytes, so a string never lands on a wider element than it spells
        .bytes => |run| {
            try comp.pool.scratch.ensureUnusedCapacity(comp.gpa, run.len);
            for (run) |byte| try comp.pool.scratch.append(comp.gpa, try comp.pool.intern(
                comp.gpa,
                .{ .value_int = .{ .type = .u8_type, .value = byte } },
            ));
        },
        .refused => |refusal| {
            try check.failRefusal(node, refusal);
            return .poison;
        },
    };

    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = .untyped_aggregate_type,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

fn checkChar(check: *Check, node: Node.Index) Allocator.Error!Value {
    const comp = check.comp;

    switch (literal.decodeChar(check.mainTokenText(node))) {
        .codepoint => |value| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_int = .{ .type = .untyped_int_type, .value = value },
        }) },
        .refused => |refusal| {
            try check.failRefusal(node, refusal);
            return .poison;
        },
    }
}

fn failRefusal(check: *Check, node: Node.Index, refusal: literal.Refusal) Allocator.Error!void {
    try check.fail(node, .{
        .code = refusal.code,
        .message = refusal.message,
        .label = refusal.label,
        .help = refusal.help,
    });
}

/// Two checked operands and the operator between them.
const Operation = struct {
    /// The operation itself, beside the two operands.
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

    const lhs = try check.checkExpr(view.lhs, null);
    const rhs = try check.checkExpr(view.rhs, null);
    if (lhs == .diverged or rhs == .diverged) return .diverged;
    if (lhs == .poison or rhs == .poison) return .poison;
    if (try check.valueOnly(view.lhs, lhs) == false) return .poison;
    if (try check.valueOnly(view.rhs, rhs) == false) return .poison;

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

/// Folded when both sides are constants, emitted otherwise.
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

/// Every edge of a fold reports at the operator.
fn settleFold(
    check: *Check,
    node: Node.Index,
    op_token: Token.Index,
    folded: Pool.Fold,
) Allocator.Error!Value {
    const comp = check.comp;
    const report: Compilation.Report = switch (folded) {
        .value => |value| return .{ .constant = value },
        .truth => |truth| {
            const bools = try check.boolType(node);
            return .{ .constant = try check.truthValue(bools, truth) };
        },
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
        .does_not_fit => |missed| .{
            .code = .does_not_fit,
            .message = try comp.fmt("{d} does not fit in {s}", .{
                missed.value,
                try comp.typeName(missed.type),
            }),
            .label = "past the type's edge",
        },
        .mismatch => |pair| {
            try check.failMixedTypes(op_token, pair.left, pair.right, operand_help);
            return .poison;
        },
        .bad_operand => |operand_type| {
            try check.reportBadOperand(op_token, operand_type);
            return .poison;
        },
    };
    try check.failToken(op_token, report);
    return .poison;
}

const operand_help = "nothing converts on its own, so give both sides one type";

const range_help = "the ends of a range take each other's type, and nothing converts on its own";

/// Two types that will not meet, named at whatever stands between them.
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
    const left = Pool.sharedType(check.typeOf(it.lhs), check.typeOf(it.rhs)) orelse {
        try check.failMixedTypes(
            it.op_token,
            check.typeOf(it.lhs),
            check.typeOf(it.rhs),
            operand_help,
        );
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
    const result = try check.emit(it.node, how.tag, result_type, .{
        .bin = .{ .lhs = refOf(lhs), .rhs = refOf(rhs) },
    });
    return runtimeValue(result, result_type);
}

const Lowering = struct {
    tag: IR.Inst.Tag,
    takes: Takes = .number,
    /// A comparison answers `bool`, and everything else the shared type.
    compares: bool = false,
};

/// What the type both sides share has to be. Bit work and `%` have no meaning
/// on a float, and equality reaches past a number to an address.
const Takes = enum { number, whole, scalar };

/// The one place an operator becomes an instruction.
fn loweringOf(op: AST.BinaryOp) Lowering {
    return switch (op) {
        .add => .{ .tag = .add },
        .sub => .{ .tag = .sub },
        .mul => .{ .tag = .mul },
        .div => .{ .tag = .div },
        .mod => .{ .tag = .mod, .takes = .whole },
        .bit_and => .{ .tag = .bit_and, .takes = .whole },
        .bit_or => .{ .tag = .bit_or, .takes = .whole },
        .bit_xor => .{ .tag = .bit_xor, .takes = .whole },
        .shift_left => .{ .tag = .shift_left, .takes = .whole },
        .shift_right => .{ .tag = .shift_right, .takes = .whole },
        .equal => .{ .tag = .cmp_eq, .takes = .scalar, .compares = true },
        .not_equal => .{ .tag = .cmp_ne, .takes = .scalar, .compares = true },
        .less_than => .{ .tag = .cmp_lt, .compares = true },
        .less_or_equal => .{ .tag = .cmp_le, .compares = true },
        .greater_than => .{ .tag = .cmp_gt, .compares = true },
        .greater_or_equal => .{ .tag = .cmp_ge, .compares = true },
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
    const lhs = try check.checkExpr(view.lhs, null);
    const bools = try check.boolType(view.lhs);
    const lhs_met = try check.coerce(lhs, bools, view.lhs);
    if (lhs_met == .poison) {
        _ = try check.checkExpr(view.rhs, null);
        return .poison;
    }

    if (lhs_met == .constant) {
        const truth = check.truthOf(bools, lhs_met.constant) orelse return .poison;
        // a side the constant decided is never entered, so it is never checked
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
    // the right side runs knowing the left held, so its proof holds here
    const facts_mark: u32 = @intCast(check.body().facts.items.len);
    defer check.body().facts.shrinkRetainingCapacity(facts_mark);

    const narrows_mark = check.body().narrows.items.len;
    try check.applyFacts(try check.gatherSpine(view.lhs));
    const rhs = try check.checkExpr(view.rhs, null);
    const rhs_met = try check.coerce(rhs, bools, view.rhs);
    if (rhs_met != .diverged) try check.emitStore(view.rhs, slot, refOf(rhs_met));
    check.body().narrows.shrinkRetainingCapacity(narrows_mark);
    if (check.blockOpen()) check.endBlock(.{ .jump = join });

    check.startBlock(join);
    check.body().reachable = entry_reachable;
    const loaded = try check.emitOne(node, .load, bools, slot);
    return runtimeValue(loaded, bools);
}

/// The first member of `e`, or else `f`.
fn checkOr(check: *Check, view: AST.View.Binary, hint: ?Pool.Index) Allocator.Error!Value {
    assert(view.op == .bool_or);
    // both sides are asked for the first member, so both are hinted with it
    const lhs = try check.checkExpr(view.lhs, hint);
    if (lhs == .diverged) return .diverged;
    if (lhs == .poison) {
        _ = try check.checkExpr(view.rhs, null);
        return .poison;
    }
    if (try check.valueOnly(view.lhs, lhs) == false) return .poison;

    const found = check.typeOf(lhs);
    if (check.comp.pool.isUnion(found) == false) {
        try check.failNotUnion(view.lhs, found, "'or' splits a union");
        return .poison;
    }
    if (check.builder == null) {
        assert(lhs == .constant);
        return check.checkOrFold(view.rhs, lhs.constant, found);
    }
    return check.checkOrSplit(view.lhs, refOf(lhs), found, view.rhs, .none);
}

/// The constants-only fold. Holding the first member decides, and `f` is never entered.
fn checkOrFold(
    check: *Check,
    rhs_node: Node.Index,
    lhs: Pool.Index,
    lhs_type: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(check.builder == null);
    assert(comp.pool.typeOfValue(lhs) == lhs_type);

    const held = comp.pool.keyOf(lhs).value_union.value;
    const first = comp.pool.firstMember(lhs_type);
    if (comp.pool.typeOfValue(held) == first) {
        return .{ .constant = held };
    }

    const rhs = try check.checkExpr(rhs_node, first);
    // the right side may be the first member, or everything the left could be
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
    const lhs = try check.checkExpr(view.lhs, hint);
    if (lhs == .diverged) return .diverged;
    if (lhs == .poison) return .poison;
    if (try check.valueOnly(view.lhs, lhs) == false) return .poison;

    const found = check.typeOf(lhs);
    if (comp.pool.isUnion(found) == false) {
        try check.failNotUnion(node, found, "'or' with a handler splits a union");
        return .poison;
    }
    return check.checkOrSplit(view.lhs, refOf(lhs), found, view.block, view.binder.toOptional());
}

/// The first member, or else the right side. The handler form binds the rest.
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
    const rest = try comp.pool.unionWithout(comp.gpa, lhs_type, first);

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
        // `or return` sends the rest up, unchanged
        const rest_value = try check.emitOne(rhs_node, .union_narrow, rest, lhs);
        const met = try check.coerce(runtimeValue(rest_value, rest), builder.return_type, rhs_node);
        try check.unwindScopesTo(0);
        check.endBlock(.{ .ret = refOf(met) });
    } else {
        // the right side runs knowing the left failed, so its proof holds
        const facts_mark: u32 = @intCast(builder.facts.items.len);
        defer builder.facts.shrinkRetainingCapacity(facts_mark);

        const narrows_mark = builder.narrows.items.len;
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
                try check.emitOne(rhs_node, .union_init, lhs_type, refOf(met));
            try check.emitStore(rhs_node, slot, settled);
        }
        builder.narrows.shrinkRetainingCapacity(narrows_mark);
        if (check.blockOpen()) check.endBlock(.{ .jump = join });
    }

    check.startBlock(join);
    builder.reachable = entry_reachable;
    const loaded = try check.emitOne(lhs_node, .load, lhs_type, slot);
    if (widened) return runtimeValue(loaded, lhs_type);
    const narrowed = try check.emitOne(lhs_node, .union_narrow, first, loaded);
    return runtimeValue(narrowed, first);
}

/// A bare `return` after `or`, in a function with something to send up.
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
    const ref = try check.emitOne(binder_node, .union_narrow, rest, lhs);
    try check.declareLocal(.{
        .name = name,
        .node = binder_node,
        .kind = .let_value,
        .payload = .{ .ref = ref },
        .type = rest,
    }, binder_node);
}

fn checkUnary(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (view.op == .address_of) return check.checkAddressOf(node, view);

    const operand = try check.checkExpr(view.operand, null);
    if (operand == .diverged) return .diverged;
    if (operand == .poison) return .poison;
    if (try check.valueOnly(view.operand, operand) == false) return .poison;

    if (operand == .constant) {
        const folded: Pool.Fold = switch (view.op) {
            .negate => try comp.pool.foldNegate(comp.gpa, operand.constant),
            .bool_not => not: {
                const bools = try check.boolType(view.operand);
                if (bools == .poison) break :not .{ .value = .poison };
                const truth = check.truthOf(bools, operand.constant) orelse
                    break :not .{ .bad_operand = comp.pool.typeOfValue(operand.constant) };
                break :not .{ .truth = !truth };
            },
            .bit_not => try comp.pool.foldBitNot(comp.gpa, operand.constant),
            .address_of => unreachable,
        };
        return check.settleFold(view.operand, view.op_token, folded);
    }

    const found = check.typeOf(operand);
    switch (view.op) {
        .address_of => unreachable,
        .negate => {
            const signed = switch (found) {
                .i8_type, .i16_type, .i32_type, .i64_type => true,
                .f32_type, .f64_type => true,
                else => false,
            };
            if (signed == false) {
                return check.reportBadUnary(view, found, "needs a signed number");
            }
            const result = try check.emitOne(node, .negate, found, refOf(operand));
            return runtimeValue(result, found);
        },
        .bool_not => {
            const bools = try check.boolType(view.operand);
            const met = try check.coerce(operand, bools, view.operand);
            if (met == .poison) return .poison;
            const result = try check.emitOne(node, .not, bools, refOf(met));
            return runtimeValue(result, bools);
        },
        .bit_not => {
            if (Pool.isInteger(found) == false) {
                return check.reportBadUnary(view, found, "needs an integer");
            }
            const result = try check.emitOne(node, .bit_not, found, refOf(operand));
            return runtimeValue(result, found);
        },
    }
}

fn reportBadUnary(
    check: *Check,
    view: AST.View.Unary,
    found: Pool.Index,
    wants: []const u8,
) Allocator.Error!Value {
    try check.failToken(view.op_token, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'{s}' {s}, and this is {s}", .{
            check.tree.tokenSlice(view.op_token),
            wants,
            try check.comp.typeName(found),
        }),
        .label = "wrong operand type",
    });
    return .poison;
}

/// `&x`, which spills to a temporary when `x` has no address of its own.
fn checkAddressOf(check: *Check, node: Node.Index, view: AST.View.Unary) Allocator.Error!Value {
    const comp = check.comp;
    if (check.builder == null) return check.needRuntime(node, "taking an address");

    const place = try check.checkPlace(view.operand) orelse return .poison;
    if (check.typeCanHold(place.type) == false) {
        try check.failToken(view.op_token, .{
            .code = .type_mismatch,
            .message = try comp.fmt("'&' needs a value with a type, and this is {s}", .{
                try comp.typeName(place.type),
            }),
            .label = "nothing to point at",
            .help = "give the value a type first, as in 'let n: i64 = 10'",
        });
        return .poison;
    }
    const addressed = try check.placeAddress(place) orelse return .poison;
    return runtimeValue(addressed.ref, try check.pointerTo(addressed.type, addressed.mutable));
}

fn checkFieldAccess(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
) Allocator.Error!Value {
    const comp = check.comp;
    const base = try check.checkExpr(view.lhs, null);
    const name_text = check.tree.tokenSlice(view.name_token);

    switch (base) {
        .poison => return .poison,
        .diverged => return .diverged,
        .named_module => |target| {
            const member = try check.moduleMember(target, node, view.name_token) orelse
                return .poison;
            return check.declAsValue(member, node);
        },
        .named_type, .named_generic => {
            try check.fail(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("'{s}' is reached through a value or called, " ++
                    "and cannot be read", .{name_text}),
                .label = "not a value",
            });
            return .poison;
        },
        .named_fn => {
            try check.failFieldOnFunction(view.name_token);
            return .poison;
        },
        .constant, .runtime => {
            const found = check.typeOf(base);
            return check.valueField(node, view, base, found);
        },
    }
}

/// Through a struct, or through one pointer.
fn valueField(
    check: *Check,
    node: Node.Index,
    view: AST.View.FieldAccess,
    base: Value,
    found: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;

    const reached = try check.reachField(found, view.name_token);
    const row = switch (reached.what) {
        .field => |found_row| found_row,
        .length => |length| return check.lengthValue(node, base, reached, length),
        .address => |held| return check.addressValue(node, base, reached, held),
        .reported => return .poison,
    };
    const row_type = comp.rowAt(row).type;

    // a field of a constant struct is a constant, so it needs no instruction
    if (reached.pointer == null and base == .constant and
        comp.pool.keyOf(base.constant) == .value_aggregate)
    {
        const rows = comp.instanceAt(comp.pool.keyOf(reached.owner).type_struct).rows;
        return .{ .constant = comp.pool.aggregateAt(base.constant, row.int() - rows.start) };
    }

    const operand: IR.Inst.Data = .{ .field = .{ .base = refOf(base), .row = row } };

    if (reached.pointer) |it| {
        const field_pointer = try check.pointerTo(row_type, it.mutable);
        const place = try check.emit(node, .field_ptr, field_pointer, operand);
        return runtimeValue(try check.emitOne(node, .load, row_type, place), row_type);
    }
    return runtimeValue(try check.emit(node, .field_val, row_type, operand), row_type);
}

/// What a name means on a type. Every `.name` asks this one question.
const Member = union(enum) {
    /// A field, by its absolute row.
    field: Compilation.Row.Index,
    method: Decl.Index,
    length: Length,
    address: Pool.Key.Slice,

    /// An array's is in its type, a view's is data, and both read as `u64`.
    const Length = union(enum) {
        known: u64,
        read,
    };

    /// What a site was looking for, and how a message names it.
    const Kind = enum {
        field,
        method,

        fn text(kind: Kind) []const u8 {
            return switch (kind) {
                .field => "field",
                .method => "method",
            };
        }
    };
};

const length_name = "len";
const address_name = "ptr";

fn memberOf(check: *Check, owner: Pool.Index, name: []const u8) Allocator.Error!?Member {
    switch (check.comp.pool.keyOf(owner)) {
        .type_array => |array| {
            if (std.mem.eql(u8, name, length_name) == false) return null;
            return .{ .length = .{ .known = array.len } };
        },
        .type_slice => |view| {
            if (std.mem.eql(u8, name, length_name)) return .{ .length = .read };
            if (std.mem.eql(u8, name, address_name)) return .{ .address = view };
            return null;
        },
        .type_struct => |instance| return check.structMember(instance, name),
        else => return null,
    }
}

fn structMember(
    check: *Check,
    instance: Pool.Instance,
    name: []const u8,
) Allocator.Error!?Member {
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

/// A constant where the type carries it, a read where the value does, `u64` either way.
fn lengthValue(
    check: *Check,
    node: Node.Index,
    base: Value,
    reached: Reach,
    length: Member.Length,
) Allocator.Error!Value {
    const comp = check.comp;
    switch (length) {
        .known => |count| return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_int = .{ .type = .u64_type, .value = count },
        }) },
        .read => {
            const held = try check.viewValue(node, base, reached);
            return runtimeValue(
                try check.emitOne(node, .slice_len, .u64_type, held),
                .u64_type,
            );
        },
    }
}

fn addressValue(
    check: *Check,
    node: Node.Index,
    base: Value,
    reached: Reach,
    view: Pool.Key.Slice,
) Allocator.Error!Value {
    const held = try check.viewValue(node, base, reached);
    const result = try check.pointerTo(view.child, view.mutable);
    return runtimeValue(try check.emitOne(node, .slice_ptr, result, held), result);
}

fn viewValue(
    check: *Check,
    node: Node.Index,
    base: Value,
    reached: Reach,
) Allocator.Error!Ref {
    const held = refOf(base);
    if (reached.pointer == null) return held;
    return check.emitOne(node, .load, reached.owner, held);
}

const deref_help = "'.*' reads what a pointer points at, and a field is reached with '.name'";

/// What the value points at, where it points at anything. Null once reported.
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

/// `p.x` and `p[i]` both reach into what `p` points at.
const Peeled = struct {
    /// The pointer that was followed, where there was one.
    pointer: ?Pool.Key.Pointer,
    /// The type the question is then asked of.
    owner: Pool.Index,
};

fn peelPointer(pool: *const Pool, from: Pool.Index) Peeled {
    switch (pool.keyOf(from)) {
        .type_pointer => |it| return .{ .pointer = it, .owner = it.child },
        else => return .{ .pointer = null, .owner = from },
    }
}

/// What a `.name` reaches, past one pointer. Every site asks here, so the answer is one.
const Reach = struct {
    pointer: ?Pool.Key.Pointer,
    owner: Pool.Index,
    what: What,

    const What = union(enum) {
        field: Compilation.Row.Index,
        length: Member.Length,
        address: Pool.Key.Slice,
        /// Nothing readable, and the report is already out.
        reported,
    };
};

fn reachField(check: *Check, from: Pool.Index, name_token: Token.Index) Allocator.Error!Reach {
    const peeled = peelPointer(&check.comp.pool, from);
    const owner = peeled.owner;

    const what: Reach.What = what: {
        if (try check.memberOf(owner, check.tree.tokenSlice(name_token))) |member| {
            switch (member) {
                .field => |row| break :what .{ .field = row },
                .length => |count| break :what .{ .length = count },
                .address => |view| break :what .{ .address = view },
                .method => {},
            }
        }
        try check.reportNoMember(owner, name_token, .field);
        break :what .reported;
    };
    return .{ .pointer = peeled.pointer, .owner = owner, .what = what };
}

/// Null once reported.
fn methodOf(
    check: *Check,
    owner: Pool.Index,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    if (try check.memberOf(owner, check.tree.tokenSlice(name_token))) |member| {
        switch (member) {
            .method => |decl_index| return decl_index,
            .field, .length, .address => {},
        }
    }
    try check.reportNoMember(owner, name_token, .method);
    return null;
}

/// A name that means something else says what it means, which beats a spelling guess.
fn reportNoMember(
    check: *Check,
    owner: Pool.Index,
    name_token: Token.Index,
    wanted: Member.Kind,
) Allocator.Error!void {
    const comp = check.comp;
    const name_text = check.tree.tokenSlice(name_token);

    // whatever broke the owner was reported already
    if (owner == .poison) return;

    // a constant that has not landed has no type, so no members, a different mistake
    if (owner == .untyped_aggregate_type) {
        return check.failToken(name_token, .{
            .code = .no_such_member,
            .message = "this array has no type yet, so it has no members to reach",
            .label = "no type in sight",
            .help = not_landed_help,
        });
    }

    if (try check.memberOf(owner, name_text)) |other| {
        try check.failToken(name_token, .{
            .code = .no_such_member,
            .message = switch (other) {
                .field => try comp.fmt("'{s}' is a field, so it is read rather than called", .{
                    name_text,
                }),
                .method => try comp.fmt("'{s}' is a function, so call it with '.{s}(...)'", .{
                    name_text, name_text,
                }),
                .length => try comp.fmt("'{s}' is a length, so it is read rather than called", .{
                    name_text,
                }),
                .address => try comp.fmt(
                    "'{s}' is the address a view holds, so it is read rather than called",
                    .{name_text},
                ),
            },
            .label = try comp.fmt("not a {s}", .{wanted.text()}),
        });
        return;
    }

    try check.failToken(name_token, .{
        .code = .no_such_member,
        .message = try comp.fmt("{s} has no {s} named '{s}'", .{
            try comp.typeName(owner), wanted.text(), name_text,
        }),
        .label = try comp.fmt("no such {s}", .{wanted.text()}),
        .help = try check.suggestMember(owner, name_text),
    });
}

/// Every operator that splits a union says so alike. `asks` is what it wanted.
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
    var closest: spell.Closest = .{ .target = name_text };

    switch (comp.pool.keyOf(owner)) {
        .type_array => {
            // storage keeps no address, so the bridge is what was meant
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
            for (members.start..members.end()) |raw| {
                const member = comp.declAt(.from(raw));
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

    try check.failToken(at, .{
        .code = .private,
        .message = try check.comp.fmt("'{s}' is private to its file", .{
            check.comp.pool.stringText(decl.name),
        }),
        .label = "not public",
        .help = "mark it 'pub' to reach it from another file",
        .notes = try check.comp.notes(&.{
            check.comp.noteAt(decl.module, decl.node, "declared here"),
        }),
    });
    return false;
}

fn checkDeref(check: *Check, node: Node.Index) Allocator.Error!Value {
    const place = try check.checkPlace(node) orelse return .poison;
    const loaded = try check.placeValue(place);
    return runtimeValue(loaded, place.type);
}

/// Type arguments when the base is generic, an index otherwise.
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
            try check.fail(node, .{
                .code = .not_a_function,
                .message = "a function with its type arguments is still not a value, so call it",
                .label = "missing the call",
            });
            return .poison;
        },
        .diverged => return .diverged,
        .poison => return .poison,
        // a name that means a value is indexed the way every other value is
        .constant, .runtime => return check.checkIndexExpr(node, view),
        else => {
            try check.fail(node, .{
                .code = .generic_arguments,
                .message = "only a generic struct or function takes type arguments",
                .label = "arguments on the wrong thing",
            });
            return .poison;
        },
    }
}

const Elements = struct {
    /// The bracket every check reaching through it reports at.
    node: Node.Index,
    base: Place,
    pointer: ?Pool.Key.Pointer,
    owner: Pool.Index,
    holds: Holds,
};

/// What a base holds. Storage settles its length in its type, a view carries
/// both its count and its own permission as data.
const Holds = struct { child: Pool.Index, len: ?u64, mutable: bool };

fn holdsOf(pool: *const Pool, owner: Pool.Index) ?Holds {
    return switch (pool.keyOf(owner)) {
        .type_array => |it| .{ .child = it.child, .len = it.len, .mutable = false },
        .type_slice => |it| .{ .child = it.child, .len = null, .mutable = it.mutable },
        else => null,
    };
}

const Indexed = struct {
    elements: Elements,
    index: Index,

    /// A bracket's one value, as the index it is.
    const Index = struct {
        ref: Ref,
        /// The element it names, where the index is known before anything runs.
        at: ?u64,
    };
};

/// `a[i]` names a place, so a read is a load from it.
fn checkIndexExpr(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!Value {
    const comp = check.comp;
    if (check.rangeIn(view)) |range| return check.checkSlice(node, view, range);

    const indexed = try check.checkIndex(node, view) orelse return .poison;

    if (indexed.index.at) |at| {
        // through a pointer the elements belong to whatever it points at
        if (indexed.elements.pointer == null) {
            if (check.placeConstant(indexed.elements.base)) |aggregate| {
                return .{ .constant = comp.pool.aggregateAt(aggregate, @intCast(at)) };
            }
        }
    }

    // the fold above is the only way past here with no body to build in
    assert(check.builder != null);
    const place = try check.elementPlace(indexed.elements, indexed.index.ref) orelse
        return .poison;
    return runtimeValue(try check.placeValue(place), place.type);
}

/// The one bridge from storage to a view. Mutability follows the place the base names.
fn checkSlice(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
    range: AST.View.Range,
) Allocator.Error!Value {
    // a view is an address, and a top-level binding has nothing to address
    if (check.builder == null) return check.needRuntime(node, "making a view");

    const elements = try check.checkElements(node, view) orelse return .poison;
    const through = try check.elementsThrough(elements) orelse return .poison;
    const bounds = try check.checkRange(view.args[0], range, elements, through) orelse
        return .poison;
    try check.emitRangeCheck(elements, through, range, bounds);

    const made = try check.sliceOf(elements.holds.child, through.mutable);
    const payload = try check.emitExtra(&.{
        @intFromEnum(through.ref),
        @intFromEnum(bounds.start),
        @intFromEnum(bounds.end),
    }, &.{});
    return runtimeValue(try check.emit(node, .slice_make, made, .{ .payload = payload }), made);
}

const Bounds = struct { start: Ref, end: Ref };

/// The ends take each other's type, and a count with nothing to take is a `u64`.
fn checkRange(
    check: *Check,
    range_node: Node.Index,
    range: AST.View.Range,
    elements: Elements,
    through: Through,
) Allocator.Error!?Bounds {
    const start = try check.checkRangeEnd(range.start) orelse return null;
    const end_node = range.end.unwrap();
    const end = if (end_node) |written|
        try check.checkRangeEnd(written) orelse return null
    else
        try check.baseLength(elements, through);

    const ends = try check.settleEnds(
        range_node,
        .{ .value = start, .node = range.start },
        .{ .value = end, .node = end_node orelse range_node },
    ) orelse return null;
    if (try check.checkRangeKnown(range_node, range, elements, ends.start, ends.end) == false) {
        return null;
    }
    return .{ .start = refOf(ends.start), .end = refOf(ends.end) };
}

/// One end of a range, and where a report about it points.
const End = struct { value: Value, node: Node.Index };

const Ends = struct { start: Value, end: Value, type: Pool.Index };

/// Both ends under one type, `u64` where neither says. Null once reported.
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

/// What the constants settle, refused before anything runs, as a constant index is.
fn checkRangeKnown(
    check: *Check,
    range_node: Node.Index,
    range: AST.View.Range,
    elements: Elements,
    start: Value,
    end: Value,
) Allocator.Error!bool {
    const comp = check.comp;
    // an omitted end came from the base, so the range itself carries the caret
    const end_node = range.end.unwrap() orelse range_node;

    const from = check.countOf(start);
    const to = check.countOf(end);

    if (from) |at| {
        if (at < 0) return check.failRangeNegative(range.start, at);
    }
    if (to) |at| {
        if (at < 0) return check.failRangeNegative(end_node, at);
    }

    if (try check.rangeRunsBackwards(range_node, start, end)) return false;

    // a view carries its length as data, so only storage settles the far edge
    if (to) |high| {
        if (elements.holds.len) |count| {
            if (high > @as(i128, count)) {
                try check.fail(end_node, .{
                    .code = .out_of_range,
                    .message = try comp.fmt(
                        "this range ends at {d}, and {s} holds {d} element{s}",
                        .{ high, try comp.typeName(elements.owner), count, plural(count) },
                    ),
                    .label = "past the last element",
                });
                return false;
            }
        }
    }
    return true;
}

/// Whether the ends cross, which is refused wherever a range is written.
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

fn failRangeNegative(check: *Check, node: Node.Index, at: i128) Allocator.Error!bool {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try check.comp.fmt(
            "an end of a range counts from zero, and this one is {d}",
            .{at},
        ),
        .label = "before the first element",
    });
    return false;
}

/// One end, which is a count the way an index is. Null once reported.
fn checkRangeEnd(check: *Check, node: Node.Index) Allocator.Error!?Value {
    const comp = check.comp;
    const value = try check.checkExpr(node, null);
    if (try check.valueOnly(node, value) == false) return null;

    const found = check.typeOf(value);
    if (found == .poison) return null;
    if (Pool.isInteger(found) == false) {
        try check.fail(node, .{
            .code = .bad_operand,
            .message = try comp.fmt("an end of a range is a count, and this is {s}", .{
                try comp.typeName(found),
            }),
            .label = "not a count",
            .help = "any integer counts, and nothing else does",
        });
        return null;
    }
    return value;
}

/// What `a..` runs to. An array answers untyped, a view with the count it carries.
fn baseLength(check: *Check, elements: Elements, through: Through) Allocator.Error!Value {
    const comp = check.comp;
    const count = elements.holds.len orelse return runtimeValue(
        try check.emitOne(elements.node, .slice_len, .u64_type, through.ref),
        .u64_type,
    );
    // untyped, so a written start settles the type for both ends
    return .{ .constant = try comp.pool.intern(comp.gpa, .{
        .value_int = .{ .type = .untyped_int_type, .value = count },
    }) };
}

/// The range a bracket holds, since only what stands inside says which a bracket is.
fn rangeIn(check: *const Check, view: AST.View.Bracket) ?AST.View.Range {
    if (view.args.len != 1) return null;
    if (check.tree.nodeTag(view.args[0]) != .range_expr) return null;
    return check.tree.viewOf(view.args[0]).range_expr;
}

/// What stands inside the brackets, checked once the base was the mistake.
fn checkBracketArgs(check: *Check, view: AST.View.Bracket) Allocator.Error!void {
    for (view.args) |argument| {
        if (check.tree.nodeTag(argument) == .range_expr) {
            const range = check.tree.viewOf(argument).range_expr;
            _ = try check.checkExpr(range.start, null);
            if (range.end.unwrap()) |end| _ = try check.checkExpr(end, null);
            continue;
        }
        _ = try check.checkExpr(argument, null);
    }
}

/// Null once reported.
fn checkIndex(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Indexed {
    const elements = try check.checkElements(node, view) orelse return null;
    const index = try check.checkIndexOperand(node, view, elements) orelse return null;
    return .{ .elements = elements, .index = index };
}

/// The base as a place, past one pointer, and what it holds. Null once reported.
fn checkElements(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Elements {
    const comp = check.comp;
    assert(check.tree.nodeTag(node) == .bracket);

    const base = try check.checkPlace(view.base) orelse return null;

    const peeled = peelPointer(&comp.pool, base.type);
    const owner = peeled.owner;
    if (owner == .poison) return null;

    const holds = holdsOf(&comp.pool, owner) orelse {
        // the base is the mistake, and the brackets still hold a program
        try check.checkBracketArgs(view);
        try check.failNotIndexable(node, owner);
        return null;
    };

    return .{
        .node = node,
        .base = base,
        .pointer = peeled.pointer,
        .owner = owner,
        .holds = holds,
    };
}

/// Any integer indexes, and a constant one is answered before anything runs.
fn checkIndexOperand(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
    elements: Elements,
) Allocator.Error!?Indexed.Index {
    const comp = check.comp;
    const length = elements.holds.len;

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
    const value = try check.checkExpr(argument, null);
    if (try check.valueOnly(argument, value) == false) return null;

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
    if (value != .constant) return .{ .ref = refOf(value), .at = null };

    const written = comp.pool.keyOf(value.constant).value_int.value;

    // a view carries its length as data, so only the near edge is settled here
    const past_end = if (length) |count| written >= @as(i128, count) else false;
    if (written < 0 or past_end) {
        try check.failIndexOutOfRange(argument, written, elements.owner, length);
        return null;
    }

    var ref = refOf(value);
    if (Pool.isUntyped(found)) {
        // an index that chose no type takes u64, the type a length reads as
        const met = try check.fitValue(value.constant, .u64_type, argument);
        // the value stands inside the length, which a u64 holds by construction
        assert(met == .constant);
        ref = refOf(met);
    }

    const at: u64 = @intCast(written);
    // the pair of the bounds assertion `Pool.aggregateAt` makes on the way out
    if (length) |count| assert(at < count);
    return .{ .ref = ref, .at = at };
}

/// A constant that has not landed is a missing annotation, not an empty type.
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

fn failIndexOutOfRange(
    check: *Check,
    node: Node.Index,
    written: i128,
    owner: Pool.Index,
    length: ?u64,
) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;

    if (written < 0) {
        try check.fail(node, .{
            .code = .out_of_range,
            .message = try comp.fmt("an index counts from zero, and this one is {d}", .{written}),
            .label = "before the first element",
        });
        return;
    }
    // an index with no length to answer to is refused only for counting down
    const count = length.?;
    try check.fail(node, .{
        .code = .out_of_range,
        .message = try comp.fmt("this index is {d}, and {s} holds {d} element{s}", .{
            written,
            try comp.typeName(owner),
            count,
            plural(count),
        }),
        .label = "past the last element",
    });
}

/// The literal names the type it builds, or takes it from where it lands.
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
            // the written type where there is one, the literal itself otherwise
            try check.fail(view.type_expr.unwrap() orelse node, .{
                .code = .not_a_type,
                .message = try comp.fmt("{s} has no fields to give", .{
                    try comp.typeName(wanted),
                }),
                .label = "not a struct",
            });
            return .poison;
        },
    };

    try comp.ensureRows(instance);
    const rows = comp.instanceAt(instance).rows;

    // one slot per field, in declaration order
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

        const row = switch ((try check.reachField(wanted, field_init.name_token)).what) {
            .field => |found| found,
            // the type was settled a struct above, and only a carrier has these
            .length, .address => unreachable,
            .reported => {
                _ = try check.checkExpr(field_init.value, null);
                clean = false;
                continue;
            },
        };
        const position: u32 = row.int() - rows.start;

        if (comp.operands.items[start + position].initializer.unwrap()) |first| {
            try check.failToken(field_init.name_token, .{
                .code = .redeclared,
                .message = try comp.fmt("'{s}' is given twice", .{
                    check.tree.tokenSlice(field_init.name_token),
                }),
                .label = "given again here",
                .notes = try comp.notes(&.{
                    comp.noteAt(check.module_index, first, "first given here"),
                }),
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

    var missing: ?[]const u8 = null;
    for (0..rows.len) |position| {
        if (comp.operands.items[start + position].initializer != .none) continue;
        const name = comp.pool.stringText(comp.rowAt(.from(rows.at(@intCast(position)))).name);
        missing = try quotedList(comp, missing, name);
    }
    if (missing) |names| {
        try check.fail(node, .{
            .code = .missing_field,
            .message = try comp.fmt("this literal leaves out {s}", .{names}),
            .label = "incomplete",
            .help = "every field of the struct must be present, and there are no defaults",
        });
        return .poison;
    }
    if (clean == false) return .poison;

    return check.settleAggregate(node, wanted, comp.operands.items[start..]);
}

/// The type the literal writes, or the one it lands on. Null once reported.
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

    // nothing asked for a value, so nothing says which struct to build
    const landing = hint orelse .void_type;
    if (landing == .poison) return null;
    if (landing != .void_type and check.comp.pool.isUnion(landing) == false) return landing;

    try check.failUnnamedLiteral(node, landing);
    return null;
}

fn failUnnamedLiteral(check: *Check, node: Node.Index, landing: Pool.Index) Allocator.Error!void {
    @branchHint(.cold);
    const comp = check.comp;

    if (landing == .void_type) {
        return check.fail(node, .{
            .code = .var_needs_type,
            .message = "nothing here says which struct this builds",
            .label = "no type in sight",
            .help = "name it, as in 'Point.{ x: 1 }', or annotate what it feeds",
        });
    }
    try check.fail(node, .{
        .code = .var_needs_type,
        .message = try comp.fmt(
            "this lands on '{s}', which lists several types, and nothing says which is built",
            .{try comp.typeName(landing)},
        ),
        .label = "which member?",
        .help = "name the struct, as in 'Point.{ x: 1 }'",
    });
}

/// A literal folds when every part is a constant and emits when one is not.
fn settleAggregate(
    check: *Check,
    node: Node.Index,
    type_index: Pool.Index,
    operands: []const Operand,
) Allocator.Error!Value {
    var all_constant = true;
    for (operands) |operand| {
        if (operand.value != .constant) all_constant = false;
    }
    if (all_constant) return check.internAggregate(type_index, operands);

    if (check.builder == null) {
        try check.fail(node, .{
            .code = .not_constant,
            .message = "a top-level binding must be a constant, and part of this literal is not",
            .label = "not a constant",
        });
        return .poison;
    }

    const payload = try check.emitExtra(&.{@intCast(operands.len)}, operands);
    const result = try check.emit(node, .aggregate_init, type_index, .{ .payload = payload });
    return runtimeValue(result, type_index);
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
    for (operands) |operand| {
        comp.pool.scratch.appendAssumeCapacity(operand.value.constant);
    }

    return .{ .constant = try comp.pool.intern(comp.gpa, .{ .value_aggregate = .{
        .type = type_index,
        .elems = comp.pool.scratch.items[mark..],
    } }) };
}

fn checkArrayLiteral(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const comp = check.comp;
    const elements = check.tree.viewOf(node).array_literal;

    // a literal names no type, so where it lands is the only thing that can
    var target: ?Pool.Key.Array = null;
    var viewed = false;

    if (hint) |found| switch (comp.pool.keyOf(found)) {
        .type_array => |array| target = array,
        .type_slice => viewed = true,
        else => {},
    };

    const element_hint: ?Pool.Index = element: {
        if (target) |array| break :element array.child;
        if (viewed) break :element comp.pool.keyOf(hint.?).type_slice.child;
        break :element null;
    };

    const start = comp.operands.items.len;
    defer comp.operands.shrinkRetainingCapacity(start);
    try comp.operands.ensureUnusedCapacity(comp.gpa, elements.len);

    var clean = true;
    var diverged = false;
    var all_constant = true;
    for (elements) |element| {
        const value = try check.checkExpr(element, element_hint);
        switch (value) {
            .constant => {},
            .runtime => all_constant = false,
            .diverged => {
                diverged = true;
                continue;
            },
            .poison => {
                clean = false;
                continue;
            },
            else => {
                try check.reportNotValue(element, value);
                clean = false;
                continue;
            },
        }
        comp.operands.appendAssumeCapacity(.{ .value = value, .initializer = .none });
    }
    if (diverged) return .diverged;
    if (clean == false) return .poison;

    const array = target orelse {
        // nothing chose, so the literal stays unchosen and fits where it lands
        if (all_constant) {
            return check.internAggregate(.untyped_aggregate_type, comp.operands.items[start..]);
        }
        // a view is an address, and only what the program owns has one to give
        if (viewed) {
            try check.fail(node, .{
                .code = .not_constant,
                .message = "a view needs bytes the program owns, and part of this " ++
                    "array is settled at run time",
                .label = "not a constant",
                .help = "bind it to storage first and slice that, as in " ++
                    "'var a: [4]u32 = ...' then 'a[0..]'",
            });
            return .poison;
        }
        try check.fail(node, .{
            .code = .var_needs_type,
            .message = "nothing says what type this array is",
            .label = "no type in sight",
            .help = "annotate what it feeds, as in 'let a: [2]u32 = ...'",
        });
        return .poison;
    };

    if (array.len != elements.len) {
        try check.fail(node, .{
            .code = .does_not_fit,
            .message = try comp.fmt("this literal has {d} element{s}, and {s} holds {d}", .{
                elements.len,
                plural(@intCast(elements.len)),
                try comp.typeName(hint.?),
                array.len,
            }),
            .label = "the wrong number of elements",
        });
        return .poison;
    }

    for (elements, 0..) |element, position| {
        const at = start + position;
        const met = try check.coerce(comp.operands.items[at].value, array.child, element);
        comp.operands.items[at].value = met;
        if (met == .poison) clean = false;
    }
    if (clean == false) return .poison;

    return check.settleAggregate(node, hint.?, comp.operands.items[start..]);
}

/// A header, then one ref per operand, as `Func.callAt` reads it back.
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

/// Every call goes through here. Reads the substituted signature, never a body.
fn checkCall(check: *Check, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const view = check.tree.viewOf(node).call;
    if (view.args.len > call_args_max) {
        try check.fail(node, .{
            .code = .wrong_arity,
            .message = try check.comp.fmt("a call takes at most {d} arguments", .{call_args_max}),
        });
        return .poison;
    }

    const callee = try check.resolveCallee(view.callee) orelse {
        for (view.args) |argument| _ = try check.checkExpr(argument, null);
        return .poison;
    };
    switch (callee.kind) {
        .builtin => |which| {
            return which.call(check, node, callee.explicit orelse &.{}, view.args, hint);
        },
        else => return check.checkCallResolved(node, callee, view.args, hint),
    }
}

/// A method waits for its receiver type, so the receiver is walked once.
const Callee = struct {
    kind: Kind,
    /// The `[T, U]` written at the call site.
    explicit: ?[]const Node.Index,

    const Kind = union(enum) {
        /// A plain function, or one reached through a module.
        direct: Decl.Index,
        /// `Type.f(...)`, whose arguments pass exactly as written.
        static: struct { decl: Decl.Index, owner: Pool.Instance },
        /// `value.f(...)`, where the value is the receiver.
        method: struct { receiver: Node.Index, name_token: Token.Index },
        /// An operation the compiler performs itself.
        builtin: Builtin,
    };
};

/// Without evaluating a receiver or an argument. Null once reported.
fn resolveCallee(check: *Check, callee_node: Node.Index) Allocator.Error!?Callee {
    switch (check.tree.viewOf(callee_node)) {
        .builtin => |name_token| {
            const which = try Builtin.resolve(check, name_token) orelse return null;
            return .{ .kind = .{ .builtin = which }, .explicit = null };
        },
        .field_access => |access| return check.resolveCalleeMember(callee_node, access),
        .bracket => |bracket| {
            var callee = switch (check.tree.viewOf(bracket.base)) {
                .builtin => |name_token| callee: {
                    const which = try Builtin.resolve(check, name_token) orelse return null;
                    break :callee Callee{ .kind = .{ .builtin = which }, .explicit = null };
                },
                .field_access => |access| try check.resolveCalleeMember(bracket.base, access) orelse
                    return null,
                else => callee: {
                    const value = try check.checkExpr(bracket.base, null);
                    break :callee try check.calleeOfValue(bracket.base, value) orelse
                        return null;
                },
            };

            if (bracket.args.len > type_params_max) {
                try check.fail(callee_node, .{
                    .code = .generic_arguments,
                    .message = try check.comp.fmt(
                        "a call takes at most {d} type arguments",
                        .{type_params_max},
                    ),
                });
                return null;
            }
            callee.explicit = bracket.args;
            return callee;
        },
        else => {
            const value = try check.checkExpr(callee_node, null);
            return check.calleeOfValue(callee_node, value);
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
                const member = try check.moduleMember(target, callee_node, access.name_token) orelse
                    return null;
                const value = try check.declAsValue(member, callee_node);
                return check.calleeOfValue(callee_node, value);
            },
            .named_type => |type_index| {
                switch (comp.pool.keyOf(type_index)) {
                    .type_struct => |owner| {
                        const member = try check.methodOf(type_index, access.name_token) orelse
                            return null;
                        if (try check.memberIsVisible(member, access.name_token) == false) {
                            return null;
                        }
                        return .{
                            .kind = .{ .static = .{ .decl = member, .owner = owner } },
                            .explicit = null,
                        };
                    },
                    else => {
                        try check.failToken(access.name_token, .{
                            .code = .no_such_member,
                            .message = try comp.fmt("{s} has no functions to call", .{
                                try comp.typeName(type_index),
                            }),
                            .label = "nothing here",
                        });
                        return null;
                    },
                }
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
            // a pure name resolved to a constant is still a receiver
            .constant, .runtime => {},
        }
    }

    return .{
        .kind = .{ .method = .{ .receiver = access.lhs, .name_token = access.name_token } },
        .explicit = null,
    };
}

/// A chain of pure names rooted outside the locals, so checking cannot emit.
fn baseIsNamespace(check: *const Check, node: Node.Index) bool {
    var current = node;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        switch (check.tree.nodeTag(current)) {
            .ident => {
                const text = check.mainTokenText(current);
                if (check.findLocal(text) != null) return false;
                return true;
            },
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
        .named_fn => |decl_index| return .{
            .kind = .{ .direct = decl_index },
            .explicit = null,
        },
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

/// Receiver, type arguments, signature, arguments, then the call or primitive.
fn checkCallResolved(
    check: *Check,
    node: Node.Index,
    callee: Callee,
    args: []const Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;

    // the receiver is written first, so it is evaluated first
    var receiver_place: ?Place = null;
    var receiver_node: ?Node.Index = null;
    var owner_args: []const Pool.Index = &.{};
    const decl_index: Decl.Index = switch (callee.kind) {
        .builtin => unreachable,
        .direct => |direct| direct,
        .static => |static| static: {
            owner_args = comp.instanceArgs(static.owner);
            break :static static.decl;
        },
        .method => |method| method: {
            const place = try check.checkPlace(method.receiver) orelse return .poison;
            if (place.type == .poison) return .poison;
            receiver_place = place;
            receiver_node = method.receiver;

            // only a struct declares one, so finding a method proves the owner
            const type_struct = peelPointer(&comp.pool, place.type).owner;
            const member = try check.methodOf(type_struct, method.name_token) orelse
                return .poison;
            if (try check.memberIsVisible(member, method.name_token) == false) return .poison;

            owner_args = comp.instanceArgs(comp.pool.keyOf(type_struct).type_struct);
            break :method member;
        },
    };

    const decl = comp.declAt(decl_index);
    const fn_name = comp.pool.stringText(decl.name);
    const own_count = comp.typeParamCount(decl_index);

    // the owner's arguments move under instantiation
    var full_args: [bindings_max]Pool.Index = undefined;
    assert(owner_args.len <= type_params_max);
    assert(own_count <= type_params_max);
    assert(owner_args.len + own_count <= full_args.len);
    @memcpy(full_args[0..owner_args.len], owner_args);
    const owner_count: u32 = @intCast(owner_args.len);

    const mark: u32 = @intCast(comp.operands.items.len);
    defer comp.operands.shrinkRetainingCapacity(mark);

    var inferred = false;
    if (callee.explicit) |explicit| {
        if (explicit.len != own_count) {
            try check.fail(node, .{
                .code = .generic_arguments,
                .message = try comp.fmt("'{s}' takes {d} type argument{s}, and this writes {d}", .{
                    fn_name, own_count, plural(own_count), explicit.len,
                }),
                .label = "wrong number of arguments",
                .notes = try comp.notes(&.{
                    comp.noteAt(decl.module, decl.node, "declared here"),
                }),
            });
            return .poison;
        }
        for (explicit, 0..) |argument, position| {
            const resolved = try check.resolveWrittenType(argument);
            if (resolved == .poison) return .poison;
            full_args[owner_count + position] = resolved;
        }
    } else if (own_count > 0) {
        const solved = try check.inferTypeArguments(
            node,
            decl_index,
            receiver_place != null,
            args,
            hint,
            full_args[owner_count..][0..own_count],
        );
        if (solved == false) return .poison;
        inferred = true;
    }
    const start: u32 = if (inferred) mark + @as(u32, @intCast(args.len)) else mark;

    const instance = try comp.instantiate(
        decl_index,
        full_args[0 .. owner_count + own_count],
        check.origin(node),
    );
    try comp.ensure(.of(.signature, instance), check.origin(node));
    if (comp.instanceAt(instance).rows_state != .done) return .poison;
    try comp.enqueueBody(instance);
    const return_type = comp.instanceType(instance);

    // a receiver consumes the first parameter
    const rows = comp.instanceAt(instance).rows;
    var receiver_count: u32 = 0;
    if (receiver_place) |place| {
        if (rows.len == 0) {
            try check.fail(node, .{
                .code = .wrong_arity,
                .message = try comp.fmt("'{s}' takes no parameters, so it has no receiver", .{
                    fn_name,
                }),
                .label = "not a method",
                .help = "call it through the type instead",
                .notes = try comp.notes(&.{
                    comp.noteAt(decl.module, decl.node, "declared here"),
                }),
            });
            return .poison;
        }
        const self_type = comp.rowAt(.from(rows.at(0))).type;
        const receiver = try check.adaptReceiver(receiver_node.?, place, self_type, fn_name) orelse
            return .poison;
        try comp.operands.append(comp.gpa, .{
            .value = runtimeValue(receiver, self_type),
            .initializer = .none,
        });
        receiver_count = 1;
    }

    const expected = rows.len - receiver_count;
    if (args.len != expected) {
        try check.fail(node, .{
            .code = .wrong_arity,
            .message = try comp.fmt("'{s}' takes {d} argument{s}, and this call has {d}", .{
                fn_name, expected, plural(expected), args.len,
            }),
            .label = "wrong number of arguments",
            .notes = try comp.notes(&.{
                comp.noteAt(decl.module, decl.node, "declared here"),
            }),
        });
        if (inferred == false) {
            for (args) |argument| _ = try check.checkExpr(argument, null);
        }
        return .poison;
    }

    var clean = true;
    for (args, 0..) |argument, position| {
        const at = receiver_count + @as(u32, @intCast(position));
        const row_type = comp.rowAt(.from(rows.at(at))).type;
        const early: ?Value = if (inferred) comp.operands.items[mark + position].value else null;
        const met = try check.checkArgument(argument, row_type, early);
        if (met == .poison) clean = false;
        try comp.operands.append(comp.gpa, .{ .value = met, .initializer = .none });
    }
    if (clean == false) return .poison;
    assert(comp.operands.items.len == start + receiver_count + args.len);

    const operands = comp.operands.items[start..];
    const payload = try check.emitExtra(&.{ instance.int(), @intCast(operands.len) }, operands);

    const result = try check.emit(node, .call, return_type, .{ .payload = payload });
    return runtimeValue(result, return_type);
}

pub fn plural(count: u64) []const u8 {
    return if (count == 1) "" else "s";
}

/// Names a message reads out, each quoted, `so_far` null before the first.
fn quotedList(
    comp: *Compilation,
    so_far: ?[]const u8,
    name: []const u8,
) Allocator.Error![]const u8 {
    const earlier = so_far orelse return comp.fmt("'{s}'", .{name});
    return comp.fmt("{s}, '{s}'", .{ earlier, name });
}

/// Coerced to its parameter type. Never checked twice, because checking emits.
fn checkArgument(
    check: *Check,
    argument: Node.Index,
    row_type: Pool.Index,
    early: ?Value,
) Allocator.Error!Value {
    if (early) |value| return check.coerce(value, row_type, argument);

    const value = try check.checkExpr(argument, row_type);
    return check.coerce(value, row_type, argument);
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

    // in source order, so evaluation order survives
    const early: u32 = @intCast(comp.operands.items.len);
    for (args) |argument| {
        const value = try check.checkExpr(argument, null);
        try comp.operands.append(comp.gpa, .{ .value = value, .initializer = .none });
    }

    const receiver_rows: u32 = if (has_receiver) 1 else 0;
    for (fn_view.type_params, 0..) |type_param, param_position| {
        const wanted = owner_tree.tokenSlice(owner_tree.nodeMainToken(type_param));
        const from_hint = hintFor(&comp.pool, owner_tree, fn_view, wanted, hint);

        const pin = switch (check.pinnedType(
            owner_tree,
            fn_view,
            wanted,
            receiver_rows,
            @intCast(args.len),
            early,
        )) {
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

        const found = check.typeOf(comp.operands.items[early + pin.argument].value);
        if (Pool.isUntyped(found)) {
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

        // the parameter as it was written, which names the shape without knowing T
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

/// What the arguments said about one type parameter.
const Pinned = union(enum) {
    type: Pool.Index,
    /// No argument had a type to read, and this is the parameter a report names.
    unread: Pin,
    /// An argument was already refused.
    poison,
    /// No value parameter is written in the type parameter.
    none,
};

/// Each parameter written in the type parameter is read until one has a type to give.
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
    var from: u32 = 0;
    while (pinFor(tree, fn_view, wanted, receiver_rows, from)) |pin| {
        from = pin.parameter + 1;
        if (first == null) first = pin;
        if (pin.argument >= args_len) continue;

        const found = check.typeOf(comp.operands.items[early + pin.argument].value);
        if (found == .poison) return .poison;
        if (Pool.isUntyped(found)) continue;

        const peeled = peelToTypeParam(&comp.pool, tree, pin.written, found) orelse continue;
        return .{ .type = peeled };
    }

    const named = first orelse return .none;
    return .{ .unread = named };
}

/// The hint, read through whatever the return type is written in, as an argument is.
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
    // a union names no one member, so only the wrappers down to the parameter are read
    if (namesTypeParam(tree, returned, wanted) == false) return null;
    return peelToTypeParam(pool, tree, returned, usable);
}

const Pin = struct { parameter: u32, argument: u32, written: Node.Index };

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

/// The first parameter from `from` on written as wrappers down to it, `*T` and `[]T` alike.
fn pinFor(
    tree: *const AST,
    fn_view: AST.View.FnDecl,
    wanted: []const u8,
    receiver_rows: u32,
    from: u32,
) ?Pin {
    for (fn_view.params, 0..) |param_node, position| {
        if (position < from) continue;
        if (tree.nodeTag(param_node) != .param) continue;
        if (position < receiver_rows) continue;
        const param = tree.viewOf(param_node).param;
        if (namesTypeParam(tree, param.type_expr, wanted) == false) continue;
        return .{
            .parameter = @intCast(position),
            .argument = @intCast(position - receiver_rows),
            .written = param.type_expr,
        };
    }
    return null;
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

/// The argument's type with the written wrappers off. Null where the shapes disagree.
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

/// As the first argument, in whichever form the declaration asked for.
fn adaptReceiver(
    check: *Check,
    receiver_node: Node.Index,
    place: Place,
    self_type: Pool.Index,
    fn_name: []const u8,
) Allocator.Error!?Ref {
    const comp = check.comp;
    assert(place.type != .poison);

    switch (comp.pool.keyOf(self_type)) {
        .type_pointer => |wanted| {
            // the receiver may already be the pointer, or need its address
            if (place.type == self_type) {
                return try check.placeValue(place);
            }
            const place_key = comp.pool.keyOf(place.type);
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
                if (wanted.mutable and place.mutable == false) {
                    try check.reportReceiverImmutable(receiver_node, place, fn_name);
                    return null;
                }
                const addressed = try check.placeAddress(place) orelse return null;
                return addressed.ref;
            }
            return check.reportReceiverMismatch(receiver_node, place.type, self_type, fn_name);
        },
        else => {
            // `self: T` takes a copy
            if (place.type == self_type) {
                return try check.placeValue(place);
            }
            const place_key = comp.pool.keyOf(place.type);
            if (place_key == .type_pointer and place_key.type_pointer.child == self_type) {
                // through one pointer, the way field access does
                const pointer = try check.placeValue(place);
                return try check.emitOne(receiver_node, .load, self_type, pointer);
            }
            return check.reportReceiverMismatch(receiver_node, place.type, self_type, fn_name);
        },
    }
}

fn reportReceiverImmutable(
    check: *Check,
    node: Node.Index,
    place: Place,
    fn_name: []const u8,
) Allocator.Error!void {
    const what: []const u8 = switch (place.reason) {
        .mutable => unreachable,
        .let_bound => "was bound with 'let'",
        .param_bound => "is a parameter, a copy that dies with the call",
        .read_only => |crossed| try check.comp.fmt("sits behind a '{s}', which is read-only", .{
            try check.comp.typeName(crossed),
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

fn reportReceiverMismatch(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    self_type: Pool.Index,
    fn_name: []const u8,
) Allocator.Error!?Ref {
    try check.fail(node, .{
        .code = .type_mismatch,
        .message = try check.comp.fmt("the first parameter of '{s}' is {s}, so {s} " ++
            "cannot be its receiver", .{
            fn_name,
            try check.comp.typeName(self_type),
            try check.comp.typeName(found),
        }),
        .label = "receiver and parameter disagree",
    });
    return null;
}

/// A location a chain of names reached. A `value` spills only when pointed at.
const Place = struct {
    kind: Kind,
    /// The address for `.address`, the value itself for `.value`.
    ref: Ref,
    /// The type at this point of the chain, the pointee for `.address`.
    type: Pool.Index,
    node: Node.Index,
    mutable: bool,
    reason: Reason,
    root_name: []const u8,
    root_node: Node.Index,

    const Kind = enum { address, value };
    const Reason = union(enum) {
        mutable,
        let_bound,
        param_bound,
        /// The read-only pointer or view the chain crossed, for the message.
        read_only: Pool.Index,
        temporary,
    };
};

/// The place a name reaches. Only a `var` has an address of its own, and only
/// a name a branch proved carries a narrowed one.
fn localPlace(
    check: *const Check,
    node: Node.Index,
    index: Builder.Local.Index,
    text: []const u8,
) Place {
    const local = check.localAt(index);
    const narrow = check.activeNarrow(index);
    if (narrow != null) assert(local.kind == .let_value or local.kind == .param);

    return .{
        .kind = if (local.kind == .var_slot) .address else .value,
        .ref = switch (local.kind) {
            .var_slot => local.payload.ref,
            .let_constant => .fromConstant(local.payload.constant),
            .let_value, .param => if (narrow) |it| it.ref else local.payload.ref,
        },
        .type = if (narrow) |it| it.type else local.type,
        .node = node,
        .mutable = local.kind == .var_slot,
        .reason = switch (local.kind) {
            .var_slot => .mutable,
            .let_constant, .let_value => .let_bound,
            .param => .param_bound,
        },
        .root_name = text,
        .root_node = local.node,
    };
}

/// An expression as a location. Null once reported.
fn checkPlace(check: *Check, node: Node.Index) Allocator.Error!?Place {
    // constants-only mode has nothing to spill into, so a place is what the value is worth
    if (check.builder == null) {
        const value = try check.checkExpr(node, null);
        return check.placeOfValue(node, value, "this value");
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
            // not a local, so ordinary resolution gives the right message
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
            return check.placeOfValue(node, value, "this value");
        },
    }
}

fn placeOfValue(
    check: *Check,
    node: Node.Index,
    value: Value,
    name: []const u8,
) Allocator.Error!?Place {
    switch (value) {
        .poison, .diverged => return null,
        .constant, .runtime => {
            const reason: Place.Reason = if (std.mem.eql(u8, name, "this value"))
                .temporary
            else
                .let_bound;
            return .{
                .kind = .value,
                .ref = refOf(value),
                .type = check.typeOf(value),
                .node = node,
                .mutable = false,
                .reason = reason,
                .root_name = name,
                .root_node = node,
            };
        },
        else => {
            try check.reportNotValue(node, value);
            return null;
        },
    }
}

/// The place `p.*` names, as mutable as `p` is.
fn placeThroughPointer(
    check: *Check,
    node: Node.Index,
    operand: Node.Index,
) Allocator.Error!?Place {
    const value = try check.checkExpr(operand, null);
    switch (value) {
        .constant, .runtime => {},
        .poison, .diverged => return null,
        else => {
            try check.reportNotValue(operand, value);
            return null;
        },
    }

    const found = check.typeOf(value);
    if (found == .poison) return null;

    const pointer = try check.pointerAt(node, found, ".*", deref_help) orelse return null;
    return .{
        .kind = .address,
        .ref = refOf(value),
        .type = pointer.child,
        .node = node,
        .mutable = pointer.mutable,
        .reason = if (pointer.mutable) .mutable else .{ .read_only = found },
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

    const reached = try check.reachField(base.type, name_token);
    const row = switch (reached.what) {
        .field => |found| found,
        .length => return check.failNotAPlace(
            name_token,
            "an array's length is in its type, and a view keeps its own",
        ),
        .address => return check.failNotAPlace(
            name_token,
            "a view keeps the address it holds, so write through the view itself",
        ),
        .reported => return null,
    };
    const row_type = comp.rowAt(row).type;

    const through = try check.placeThrough(base, reached.pointer) orelse return null;
    const field_pointer = try check.pointerTo(row_type, through.mutable);
    const place = try check.emit(node, .field_ptr, field_pointer, .{
        .field = .{ .base = through.ref, .row = row },
    });
    return through.reaching(node, place, row_type);
}

/// One index step, the same shape as a field step.
fn placeIndex(
    check: *Check,
    node: Node.Index,
    view: AST.View.Bracket,
) Allocator.Error!?Place {
    // a view is made, not found, so there is nowhere to write or point
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
    return check.elementPlace(indexed.elements, indexed.index.ref);
}

/// The place an index names, as mutable as whatever it reached through.
fn elementPlace(check: *Check, elements: Elements, index: Ref) Allocator.Error!?Place {
    const element = elements.holds.child;
    // neither carrier ever holds a broken element, so an element always has one
    assert(element != .poison);
    assert(index != .none);

    const through = try check.elementsThrough(elements) orelse return null;
    try check.emitBoundsCheck(elements, through, index);

    const element_pointer = try check.pointerTo(element, through.mutable);
    const place = try check.emit(elements.node, .elem_ptr, element_pointer, .{
        .bin = .{ .lhs = through.ref, .rhs = index },
    });
    return through.reaching(elements.node, place, element);
}

fn emitBoundsCheck(
    check: *Check,
    elements: Elements,
    through: Through,
    index: Ref,
) Allocator.Error!void {
    if (settledAgainstBase(elements, index)) return;

    const length = try check.baseLengthRef(elements, through);
    _ = try check.emit(elements.node, .bounds_check, .void_type, .{
        .bin = .{ .lhs = index, .rhs = length },
    });
}

/// Storage carries its length in its type, so a constant against one was already answered.
fn settledAgainstBase(elements: Elements, count: Ref) bool {
    if (elements.holds.len == null) return false;
    return refIsConstant(count);
}

/// The count a check reads against, always a `u64`.
fn baseLengthRef(check: *Check, elements: Elements, through: Through) Allocator.Error!Ref {
    const comp = check.comp;
    const count = elements.holds.len orelse
        return check.emitOne(elements.node, .slice_len, .u64_type, through.ref);
    return .fromConstant(try comp.pool.intern(comp.gpa, .{
        .value_int = .{ .type = .u64_type, .value = count },
    }));
}

/// Answered before the view is made, since its length is what later indexes answer against.
fn emitRangeCheck(
    check: *Check,
    elements: Elements,
    through: Through,
    range: AST.View.Range,
    bounds: Bounds,
) Allocator.Error!void {
    if (refIsConstant(bounds.start) == false or refIsConstant(bounds.end) == false) {
        _ = try check.emit(elements.node, .order_check, .void_type, .{
            .bin = .{ .lhs = bounds.start, .rhs = bounds.end },
        });
    }

    // an omitted end is the base's own length, so nothing can run past it
    if (range.end == .none) return;
    if (settledAgainstBase(elements, bounds.end)) return;

    const length = try check.baseLengthRef(elements, through);
    _ = try check.emit(elements.node, .order_check, .void_type, .{
        .bin = .{ .lhs = bounds.end, .rhs = length },
    });
}

fn refIsConstant(ref: Ref) bool {
    assert(ref != .none);
    return switch (ref.unwrap()) {
        .constant => true,
        .inst => false,
    };
}

/// A view carries its own permission and leads with the address, so elements
/// reach through its value. Storage is reached through its place instead.
fn elementsThrough(check: *Check, elements: Elements) Allocator.Error!?Through {
    if (elements.holds.len != null) {
        return check.placeThrough(elements.base, elements.pointer);
    }

    var held = try check.placeValue(elements.base);
    // one pointer was followed to reach the view, so the view is read first
    if (elements.pointer != null) {
        held = try check.emitOne(elements.node, .load, elements.owner, held);
    }
    const mutable = elements.holds.mutable;
    return .{
        .ref = held,
        .mutable = mutable,
        .reason = if (mutable) .mutable else .{ .read_only = elements.owner },
        .root = elements.base,
    };
}

/// Where one step into a place starts, and what it may do once it arrives.
const Through = struct {
    /// The pointer to reach through, or the base's own address.
    ref: Ref,
    mutable: bool,
    reason: Place.Reason,
    /// Whose name a report about what was reached carries.
    root: Place,

    fn reaching(through: Through, node: Node.Index, place: Ref, type_index: Pool.Index) Place {
        return .{
            .kind = .address,
            .ref = place,
            .type = type_index,
            .node = node,
            .mutable = through.mutable,
            .reason = through.reason,
            .root_name = through.root.root_name,
            .root_node = through.root.root_node,
        };
    }
};

/// Through a pointer the reach is the pointer's own, otherwise the base's address.
fn placeThrough(
    check: *Check,
    base: Place,
    pointer: ?Pool.Key.Pointer,
) Allocator.Error!?Through {
    if (pointer) |it| {
        return .{
            .ref = try check.placeValue(base),
            .mutable = it.mutable,
            .reason = if (it.mutable) .mutable else .{ .read_only = base.type },
            .root = base,
        };
    }
    const addressed = try check.placeAddress(base) orelse return null;
    return .{
        .ref = addressed.ref,
        .mutable = addressed.mutable,
        .reason = addressed.reason,
        .root = addressed,
    };
}

/// The constant a place holds outright, where it holds one.
fn placeConstant(check: *const Check, place: Place) ?Pool.Index {
    if (place.kind != .value) return null;
    const held = switch (place.ref.unwrap()) {
        .constant => |value| value,
        .inst => return null,
    };
    return switch (check.comp.pool.keyOf(held)) {
        .value_aggregate, .value_splat => held,
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

/// Loading when the place is an address.
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

    const slot = try check.emitSlot(place.node, .empty, place.type);
    try check.emitStore(place.node, slot, place.ref);
    return .{
        .kind = .address,
        .ref = slot,
        .type = place.type,
        .node = place.node,
        .mutable = false,
        .reason = place.reason,
        .root_name = place.root_name,
        .root_node = place.root_node,
    };
}

fn reportImmutable(check: *Check, node: Node.Index, place: Place) Allocator.Error!void {
    const comp = check.comp;
    assert(place.mutable == false);

    const report: Compilation.Report = switch (place.reason) {
        .mutable => unreachable,
        .let_bound => .{
            .code = .not_assignable,
            .message = try comp.fmt("'{s}' was bound with 'let', so it cannot change", .{
                place.root_name,
            }),
            .label = "immutable",
            .help = "declare it 'var' if it needs to change",
            .notes = try comp.notes(&.{
                comp.noteAt(check.module_index, place.root_node, "bound here"),
            }),
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
        .read_only => |crossed| report: {
            const writable = switch (comp.pool.keyOf(crossed)) {
                .type_pointer => |it| try comp.fmt("*var {s}", .{try comp.typeName(it.child)}),
                .type_slice => |it| try comp.fmt("[]var {s}", .{try comp.typeName(it.child)}),
                else => unreachable,
            };
            break :report .{
                .code = .write_through_pointer,
                .message = try comp.fmt("this writes through a '{s}', which is read-only", .{
                    try comp.typeName(crossed),
                }),
                .label = "read-only",
                .help = try comp.fmt("take '{s}' to write through it", .{writable}),
            };
        },
        .temporary => .{
            .code = .not_assignable,
            .message = "this value has no home, so there is nowhere to write",
            .label = "not a place",
        },
    };
    try check.fail(node, report);
}

fn moduleMember(
    check: *Check,
    target: Module.Index,
    node: Node.Index,
    name_token: Token.Index,
) Allocator.Error!?Decl.Index {
    const name_text = check.tree.tokenSlice(name_token);
    return Module.findExported(
        check.comp,
        target,
        name_text,
        .{ .module = check.module_index, .node = node },
        name_token,
    );
}

// coercion and small shared answers

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

/// Anything with no ref of its own becomes poison.
pub fn refOf(value: Value) Ref {
    return switch (value) {
        .constant => |constant| .fromConstant(constant),
        .runtime => |runtime| runtime.ref,
        .diverged, .poison => .fromConstant(.poison),
        .named_type, .named_generic, .named_fn, .named_module => .fromConstant(.poison),
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
fn coerce(
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

            const have = comp.pool.keyOf(runtime.type);
            const want = comp.pool.keyOf(wanted);

            if (Pool.widens(runtime.type, wanted)) {
                const tag: IR.Inst.Tag = if (Pool.isFloat(wanted)) .float_widen else .int_widen;
                return runtimeValue(try check.emitOne(node, tag, wanted, runtime.ref), wanted);
            }

            // the one subtyping edge, which a view has for a pointer's reason
            if (writesThrough(&comp.pool, runtime.type, wanted)) |writable| {
                if (writable) return runtimeValue(runtime.ref, wanted);
                try check.failNeedsWritable(node, runtime.type, wanted);
                return .poison;
            }

            // membership decides, entering a union that lists the value or covers it
            if (want == .type_union) {
                const listed = if (have == .type_union)
                    comp.pool.unionCovers(wanted, runtime.type)
                else
                    comp.pool.unionHas(wanted, runtime.type);
                if (listed) {
                    const wrapped = try check.emitOne(node, .union_init, wanted, runtime.ref);
                    return runtimeValue(wrapped, wanted);
                }
            }

            return check.reportMismatch(node, value, wanted);
        },
        else => {
            try check.reportNotValue(node, value);
            return .poison;
        },
    }
}

/// Whether two types reach one child, and if so whether the first may be written through.
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

/// A constant meets a type by value.
fn fitValue(
    check: *Check,
    constant: Pool.Index,
    wanted: Pool.Index,
    node: Node.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    if (constant == .poison) return .poison;
    if (wanted == .poison) return .poison;

    const found = comp.pool.typeOfValue(constant);

    if (found != wanted and Pool.widens(found, wanted)) {
        const widened: Pool.Key = switch (comp.pool.keyOf(constant)) {
            .value_int => |it| .{ .value_int = .{ .type = wanted, .value = it.value } },
            .value_float => |it| .{ .value_float = .{ .type = wanted, .value = it.value } },
            // widening answers for a number and nothing else
            else => unreachable,
        };
        return .{ .constant = try comp.pool.intern(comp.gpa, widened) };
    }

    return switch (try comp.pool.fit(comp.gpa, constant, wanted)) {
        .value => |final| .{ .constant = final },
        .does_not_fit => fitted: {
            try check.reportDoesNotFit(node, constant, wanted);
            break :fitted .poison;
        },
        .wrong_kind => try check.reportMismatch(node, .{ .constant = constant }, wanted),
    };
}

fn reportDoesNotFit(
    check: *Check,
    node: Node.Index,
    constant: Pool.Index,
    wanted: Pool.Index,
) Allocator.Error!void {
    try check.fail(node, .{
        .code = .does_not_fit,
        .message = try check.comp.fmt("{s} does not fit in {s}", .{
            try check.comp.spellValue(constant),
            try check.comp.typeName(wanted),
        }),
        .label = "past the type's edge",
        .help = "an untyped constant takes any type its value fits, " ++
            "and this value does not fit this one",
    });
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

    // the union holds what is wanted, so what is missing is the proof
    const narrowable = found != .poison and wanted != .poison and
        comp.pool.isUnion(found) and comp.pool.isUnion(wanted) == false and
        comp.pool.unionHas(found, wanted);

    const help: []const u8 = help: {
        if (narrowable) {
            break :help try comp.fmt("narrow it first, with a guard 'is {s} or return' or " ++
                "inside the branch that proved it, and never through a 'var'", .{
                try comp.typeName(wanted),
            });
        }
        if (Pool.isSizedInt(found) and Pool.isSizedInt(wanted)) {
            break :help "not every value fits, so '@int_cast(...)' gives 'none' where one does not";
        }
        if (check.needsBridge(found, wanted)) {
            break :help "slice it to make a view of it, as in 'a[0..]'";
        }
        if (check.wantsWritableView(found, wanted)) {
            break :help "a constant makes '[]T' and never '[]var T', because the " ++
                "program's own bytes are read-only";
        }
        break :help "nothing converts on its own";
    };

    try check.fail(node, .{
        .code = .type_mismatch,
        .message = try comp.fmt("expected {s}, found {s}", .{
            try comp.typeName(wanted),
            found_name,
        }),
        .label = "the wrong type",
        .help = help,
    });
    return .poison;
}

/// Whether a constant that has not landed was asked for a view it may write through.
fn wantsWritableView(check: *const Check, found: Pool.Index, wanted: Pool.Index) bool {
    if (found != .untyped_aggregate_type) return false;
    return switch (check.comp.pool.keyOf(wanted)) {
        .type_slice => |slice| slice.mutable,
        else => false,
    };
}

/// Whether storage was handed over where a view of it was asked for
fn needsBridge(check: *const Check, found: Pool.Index, wanted: Pool.Index) bool {
    const stored = switch (check.comp.pool.keyOf(found)) {
        .type_array => |it| it.child,
        else => return false,
    };
    const viewed = switch (check.comp.pool.keyOf(wanted)) {
        .type_slice => |it| it.child,
        else => return false,
    };
    return stored == viewed;
}

pub fn valueOnly(check: *Check, node: Node.Index, value: Value) Allocator.Error!bool {
    switch (value) {
        .constant, .runtime, .poison, .diverged => return true,
        else => {
            try check.reportNotValue(node, value);
            return false;
        },
    }
}

fn runtimeOnly(tag: Node.Tag) ?[]const u8 {
    return switch (tag) {
        .if_expr => "an 'if'",
        .loop_expr => "a loop",
        .match_expr => "a 'match'",
        .block => "a block",
        .return_expr => "'return'",
        .break_expr => "'break'",
        .continue_expr => "'continue'",
        .call => "a call",
        .deref => "reading through a pointer",
        .is_expr => "an 'is' test",
        .or_bind => "an 'or' handler",
        else => null,
    };
}

fn needRuntime(check: *Check, node: Node.Index, what: []const u8) Allocator.Error!Value {
    assert(check.builder == null);
    try check.fail(node, .{
        .code = .not_constant,
        .message = try check.comp.fmt(
            "a top-level binding must be a constant, and {s} happens at run time",
            .{what},
        ),
        .label = "not a constant",
        .help = "the constant set is literals, names of constants, operators, and parentheses",
    });
    return .poison;
}

fn reportNotValue(check: *Check, node: Node.Index, value: Value) Allocator.Error!void {
    const report: Compilation.Report = switch (value) {
        .named_type, .named_generic => .{
            .code = .type_as_value,
            .message = "types are not values",
            .label = "a type, where a value belongs",
            .help = "a type appears in type positions, and as the base of a '.' access",
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
        // a value that never arrives is never complained about
        .constant, .runtime, .poison, .diverged => unreachable,
    };
    try check.fail(node, report);
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
        .help = if (equality) check.equalityHelp(operand_type) else null,
    });
}

/// What answers where one comparison cannot.
fn equalityHelp(check: *const Check, found: Pool.Index) ?[]const u8 {
    return switch (check.comp.pool.keyOf(found)) {
        .type_union => "'is' tests which member a union holds and narrows the name to it",
        .type_slice => "'std.mem.eql' compares two views element by element",
        .type_array => "slice them first, as in 'mem.eql(a[0..], b[0..])'",
        .type_struct => "compare the fields that decide it",
        else => null,
    };
}

/// `_` stands only in `_ = expression`, so every site that wanted a name reports alike.
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

/// Among locals, type parameters, this file's declarations, and the prelude.
fn suggestName(check: *Check, text: []const u8) Allocator.Error!?[]const u8 {
    const comp = check.comp;
    var closest: spell.Closest = .{ .target = text };

    if (check.builder) |builder| {
        for (builder.locals.items) |local| {
            closest.consider(comp.pool.stringText(local.name));
        }
    }
    for (check.bindings) |binding| {
        closest.consider(comp.pool.stringText(binding.name));
    }
    for (comp.declsIn(check.module.decls)) |decl| {
        if (decl.owner != .none) continue;
        closest.consider(comp.pool.stringText(decl.name));
    }
    if (comp.prelude) |prelude| {
        if (prelude != check.module_index) {
            for (comp.declsIn(comp.moduleAt(prelude).decls)) |decl| {
                if (decl.owner != .none) continue;
                closest.consider(comp.pool.stringText(decl.name));
            }
        }
    }
    for (Pool.primitive_names) |name| closest.consider(name);

    return comp.didYouMean(closest);
}

pub fn origin(check: *const Check, node: Node.Index) Compilation.Origin {
    return .{ .module = check.module_index, .node = node };
}

pub fn fail(check: *Check, node: Node.Index, report: Compilation.Report) Allocator.Error!void {
    try check.comp.reportNode(check.module_index, node, report);
}

pub fn failToken(
    check: *Check,
    token: Token.Index,
    report: Compilation.Report,
) Allocator.Error!void {
    try check.comp.reportToken(check.module_index, token, report);
}

/// Marks an unreachable block in the map `finishFunc` renumbers through.
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

    // reachability from the entry, visited marked in the map itself
    const map = builder.block_map.items;
    map[0] = 0;
    builder.frontier.appendAssumeCapacity(0);
    while (builder.frontier.pop()) |raw| {
        switch (builder.blocks.items[raw].terminator) {
            .none => unreachable,
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
            .terminator = switch (block.terminator) {
                .none => unreachable,
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
    @memcpy(into.items(.tag)[insts_start..], from.items(.tag));
    @memcpy(into.items(.type)[insts_start..], from.items(.type));
    @memcpy(into.items(.node)[insts_start..], from.items(.node));
    @memcpy(into.items(.data)[insts_start..], from.items(.data));

    // the pair of the range assertion `emit` makes on the way in
    const tree_nodes = check.tree.nodes.len;
    for (into.items(.node)[insts_start..]) |node| assert(node.int() < tree_nodes);

    const extra_start: u32 = @intCast(comp.inst_extra.items.len);
    try comp.inst_extra.appendSlice(gpa, builder.extra.items);

    try comp.funcs.append(gpa, .{
        .instance = builder.instance,
        .insts = .{ .start = insts_start, .len = inst_count },
        .extra = .{ .start = extra_start, .len = @intCast(builder.extra.items.len) },
        .blocks = .{ .start = blocks_start, .len = live_blocks },
    });

    assert(comp.instanceAt(builder.instance).func == .none);
    const index: IR.Func.Index = .from(comp.funcs.items.len - 1);
    comp.instancePtr(builder.instance).func = index.toOptional();
}

fn finishFuncVisit(map: []u32, frontier: *std.ArrayList(u32), target: u32) void {
    if (map[target] != block_dead) return;
    map[target] = 0;
    frontier.appendAssumeCapacity(target);
}

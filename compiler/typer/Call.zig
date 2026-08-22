const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const IR = @import("../IR.zig");
const Module = @import("../Module.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Builtin = @import("Builtin.zig").Builtin;
const Comptime = @import("Comptime.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");
const Place = @import("Place.zig");

const Decl = Module.Decl;
const Node = AST.Node;
const Ref = IR.Ref;
const Value = Typer.Value;
const runtimeValue = Typer.runtimeValue;
const type_params_max = Typer.type_params_max;
const bindings_max = Typer.bindings_max;
const call_args_max = Typer.call_args_max;
const type_depth_max = Typer.type_depth_max;

pub fn checkCall(typer: *Typer, node: Node.Index, hint: ?Pool.Index) Allocator.Error!Value {
    const view = typer.tree.viewOf(node).call;
    if (view.args.len > call_args_max) {
        return typer.refuse(node, .{
            .code = .wrong_arity,
            .message = try typer.comp.fmt("a call takes at most {d} arguments", .{call_args_max}),
        });
    }

    var explicit: ?[]const Node.Index = null;
    var callee_node = view.callee;
    if (typer.tree.nodeTag(callee_node) == .bracket) {
        const bracket = typer.tree.viewOf(callee_node).bracket;
        explicit = bracket.args;
        callee_node = bracket.base;
    }
    const callee = try resolveCallee(typer, callee_node) orelse return abandonCall(typer, view.args);
    if (explicit) |written| {
        if (written.len > type_params_max) {
            try typer.fail(view.callee, .{
                .code = .generic_arguments,
                .message = try typer.comp.fmt(
                    "a call takes at most {d} type arguments",
                    .{type_params_max},
                ),
            });
            return abandonCall(typer, view.args);
        }
    }

    if (callee == .builtin) {
        const which = callee.builtin;
        if (typer.builder == null and which.needsBody()) {
            const name = try typer.comp.fmt("'@{s}'", .{@tagName(which)});
            return typer.needRuntime(node, name);
        }
        return which.call(typer, node, explicit orelse &.{}, view.args, hint);
    }
    return checkCallResolved(typer, node, callee, explicit, view.args, hint);
}

fn abandonCall(typer: *Typer, args: []const Node.Index) Allocator.Error!Value {
    for (args) |argument| _ = try typer.checkExpr(argument, null);
    return .poison;
}

const Callee = union(enum) {
    builtin: Builtin,
    direct: Decl.Index,
    static: struct { decl: Decl.Index, owner: Pool.Instance },
    method: struct { node: Node.Index, receiver: Node.Index, name_token: Token.Index },
};

fn resolveCallee(typer: *Typer, node: Node.Index) Allocator.Error!?Callee {
    switch (typer.tree.viewOf(node)) {
        .builtin => |name_token| {
            const which = try Builtin.resolve(typer, name_token) orelse return null;
            return .{ .builtin = which };
        },
        .field_access => |access| return resolveCalleeMember(typer, node, access),
        else => {
            const value = try typer.checkExpr(node, null);
            return calleeOfValue(typer, node, value);
        },
    }
}

fn resolveCalleeMember(
    typer: *Typer,
    callee_node: Node.Index,
    access: AST.View.FieldAccess,
) Allocator.Error!?Callee {
    const comp = typer.comp;

    if (baseIsNamespace(typer, access.lhs)) {
        const base = try typer.checkExpr(access.lhs, null);
        switch (base) {
            .poison, .diverged => return null,
            .named_module => |target| {
                const member = try Resolve.exported(typer, target, callee_node, access.name_token) orelse
                    return null;
                typer.link(callee_node, .{ .decl = member });
                const value = try Resolve.declAsValue(typer, member, callee_node);
                return calleeOfValue(typer, callee_node, value);
            },
            .named_type => |type_index| {
                if (comp.pool.keyOf(type_index) != .type_struct) {
                    try typer.failToken(access.name_token, .{
                        .code = .no_such_member,
                        .message = try comp.fmt("{s} has no functions to call", .{
                            try comp.typeName(type_index),
                        }),
                        .label = "nothing here",
                    });
                    return null;
                }
                const member = try Expr.methodOf(typer, type_index, access.name_token) orelse return null;
                typer.link(callee_node, .{ .decl = member });
                if (try Expr.memberIsVisible(typer, member, access.name_token) == false) return null;
                return .{ .static = .{ .decl = member, .owner = comp.pool.structOf(type_index) } };
            },
            .named_generic => {
                try typer.fail(access.lhs, .{
                    .code = .generic_arguments,
                    .message = "this is generic, so write its arguments before reaching in",
                    .label = "missing type arguments",
                });
                return null;
            },
            .named_fn => {
                try Expr.failFieldOnFunction(typer, access.name_token);
                return null;
            },
            .constant, .runtime => {},
        }
    }
    return .{ .method = .{
        .node = callee_node,
        .receiver = access.lhs,
        .name_token = access.name_token,
    } };
}

pub fn baseIsNamespace(typer: *const Typer, node: Node.Index) bool {
    var current = node;
    var depth: u32 = 0;
    while (depth < type_depth_max) : (depth += 1) {
        switch (typer.tree.nodeTag(current)) {
            .ident => return typer.findLocalIndex(typer.mainTokenText(current)) == null,
            .field_access => current = typer.tree.viewOf(current).field_access.lhs,
            .bracket => current = typer.tree.viewOf(current).bracket.base,
            else => return false,
        }
    }
    return false;
}

fn calleeOfValue(typer: *Typer, node: Node.Index, value: Value) Allocator.Error!?Callee {
    const comp = typer.comp;
    switch (value) {
        .named_fn => |decl_index| return .{ .direct = decl_index },
        .poison, .diverged => return null,
        .constant, .runtime => {
            try typer.fail(node, .{
                .code = .not_a_function,
                .message = try comp.fmt("this is {s}, not a function", .{
                    try comp.typeName(typer.typeOf(value)),
                }),
                .label = "cannot be called",
            });
            return null;
        },
        .named_type, .named_generic => {
            try typer.fail(node, .{
                .code = .not_a_function,
                .message = "a type is not callable, and there are no conversions to call",
                .label = "a type",
            });
            return null;
        },
        .named_module => {
            try typer.fail(node, .{
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
    typer: *Typer,
    node: Node.Index,
    callee: Callee,
    explicit: ?[]const Node.Index,
    args: []const Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!Value {
    const comp = typer.comp;

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
            const place = try Place.checkPlace(typer, method.receiver) orelse return .poison;
            if (place.type == .poison) return .poison;
            receiver = .{ .place = place, .node = method.receiver };

            const type_struct = Expr.peelPointer(&comp.pool, place.type).owner;
            const member = try Expr.methodOf(typer, type_struct, method.name_token) orelse
                return .poison;
            typer.link(method.node, .{ .decl = member });
            if (try Expr.memberIsVisible(typer, member, method.name_token) == false) return .poison;

            owner_args = comp.instanceArgs(comp.pool.structOf(type_struct));
            break :method member;
        },
    };

    const decl = comp.declAt(decl_index);
    const fn_name = comp.pool.stringText(decl.name);
    const own_count = comp.declAt(decl_index).type_params;

    var full_args: [bindings_max]Pool.Index = undefined;
    assert(owner_args.len <= type_params_max);
    assert(own_count <= type_params_max);
    assert(owner_args.len + own_count <= full_args.len);
    @memcpy(full_args[0..owner_args.len], owner_args);
    const owner_count: u32 = @intCast(owner_args.len);

    const mark: u32 = @intCast(comp.scratch.operands.items.len);
    defer comp.scratch.operands.shrinkRetainingCapacity(mark);

    var inferred = false;
    if (explicit) |written| {
        if (written.len != own_count) {
            const declared = try comp.noteOne(decl.module, decl.node, "declared here");
            try typer.failArity(node, fn_name, .type, own_count, written.len, declared);
            return .poison;
        }
        for (written, 0..) |argument, position| {
            const resolved = try Resolve.resolveWrittenType(typer, argument);
            if (resolved == .poison) return .poison;
            full_args[owner_count + position] = resolved;
        }
    } else if (own_count > 0) {
        const solved = try inferTypeArguments(
            typer,
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

    if (try Resolve.boundsHold(typer, decl_index, full_args[owner_count..][0..own_count], node) == false) {
        return .poison;
    }

    const instance = try comp.instantiate(
        decl_index,
        full_args[0 .. owner_count + own_count],
        typer.origin(node),
    );
    try comp.ensure(.{ .head = instance }, typer.origin(node));
    if (comp.instanceAt(instance).head != .done) return .poison;
    const return_type = comp.instanceType(instance);

    const rows = comp.instanceAt(instance).rows;
    var receiver_count: u32 = 0;
    if (receiver) |it| {
        if (rows.len == 0) {
            return typer.refuse(node, .{
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
        const adapted = try adaptReceiver(typer, it.node, it.place, self_type, fn_name) orelse
            return .poison;
        try comp.scratch.operands.append(comp.gpa, .{
            .value = runtimeValue(adapted, self_type),
            .initializer = .none,
        });
        receiver_count = 1;
    }

    const expected = rows.len - receiver_count;
    if (args.len != expected) {
        const declared = try comp.noteOne(decl.module, decl.node, "declared here");
        try typer.failArity(node, fn_name, .value, expected, args.len, declared);
        if (inferred == false) {
            for (args) |argument| _ = try typer.checkExpr(argument, null);
        }
        return .poison;
    }

    // an argument is never checked twice, because checking emits
    var clean = true;
    for (args, 0..) |argument, position| {
        const at = receiver_count + @as(u32, @intCast(position));
        const row_type = comp.rowAt(.from(rows.at(at))).type;
        const value = if (inferred)
            comp.scratch.operands.items[mark + position].value
        else
            try typer.checkExpr(argument, row_type);
        const met = try typer.coerce(value, row_type, argument);
        if (met == .poison) clean = false;
        try comp.scratch.operands.append(comp.gpa, .{ .value = met, .initializer = .none });
    }
    if (clean == false) return .poison;
    assert(comp.scratch.operands.items.len == start + receiver_count + args.len);

    const operands = comp.scratch.operands.items[start..];
    if (typer.builder == null) return Comptime.call(typer, node, instance, operands);

    const payload = try typer.emitExtra(&.{ instance.int(), @intCast(operands.len) }, operands);
    return typer.emitValue(node, .call, return_type, .{ .payload = payload });
}

fn inferTypeArguments(
    typer: *Typer,
    node: Node.Index,
    decl_index: Decl.Index,
    has_receiver: bool,
    args: []const Node.Index,
    hint: ?Pool.Index,
    out: []Pool.Index,
) Allocator.Error!bool {
    const comp = typer.comp;
    const decl = comp.declAt(decl_index);
    const owner_tree = comp.treeOf(decl.module);
    const fn_view = owner_tree.viewOf(decl.node).fn_decl;
    const fn_name = comp.pool.stringText(decl.name);

    const early: u32 = @intCast(comp.scratch.operands.items.len);
    for (args) |argument| {
        const value = try typer.checkExpr(argument, null);
        try comp.scratch.operands.append(comp.gpa, .{ .value = value, .initializer = .none });
    }

    var bound_buffer: [type_params_max]Pool.Index = undefined;
    const bounds = try comp.boundsOf(decl_index, typer.origin(node), &bound_buffer) orelse &.{};

    const receiver_rows: u32 = if (has_receiver) 1 else 0;
    for (fn_view.type_params, 0..) |type_param, param_position| {
        const wanted = owner_tree.tokenSlice(owner_tree.nodeMainToken(type_param));
        const bound = Resolve.boundAt(bounds, param_position);

        const pinned = pinnedType(
            typer,
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
            const value = comp.scratch.operands.items[early + pinned.unread.argument].value;
            if (value != .constant) break :literal null;
            break :literal if (Pool.isUntyped(typer.typeOf(value))) value.constant else null;
        };
        var from_hint = hintFor(&comp.pool, owner_tree, fn_view, wanted, hint);
        if (from_hint) |hinted| {
            if (bound) |limit| from_hint = try Resolve.admittedBy(comp, limit, hinted, literal);
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
                try typer.fail(node, .{
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
            try typer.fail(node, .{
                .code = .inference_failed,
                .message = try comp.fmt("'{s}' would be pinned by an argument this call lacks", .{
                    wanted,
                }),
                .label = "too few arguments to infer from",
            });
            return false;
        }

        const value = comp.scratch.operands.items[early + pin.argument].value;
        const found = typer.typeOf(value);
        if (Pool.isUntyped(found)) {
            if (bound) |limit| if (wrapperOf(owner_tree, pin.written) == null) {
                const met = try typer.fitValue(value.constant, limit, args[pin.argument]);
                if (met != .constant) return false;
                out[param_position] = comp.pool.memberOfValue(met.constant);
                continue;
            };
            try typer.fail(args[pin.argument], .{
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
        try typer.fail(args[pin.argument], .{
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
    poison,
    none,
};

fn pinnedType(
    typer: *Typer,
    tree: *const AST,
    fn_view: AST.View.FnDecl,
    wanted: []const u8,
    receiver_rows: u32,
    args_len: u32,
    early: u32,
) Pinned {
    const comp = typer.comp;
    var first: ?Pin = null;
    for (fn_view.params, 0..) |param_node, position| {
        if (position < receiver_rows) continue;
        if (tree.nodeTag(param_node) != .param) continue;
        const written = tree.viewOf(param_node).param.type_expr;
        if (namesTypeParam(tree, written, wanted) == false) continue;

        const pin: Pin = .{ .argument = @intCast(position - receiver_rows), .written = written };
        if (first == null) first = pin;
        if (pin.argument >= args_len) continue;

        const value = comp.scratch.operands.items[early + pin.argument].value;
        const found = typer.typeOf(value);
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

const Pin = struct { argument: u32, written: Node.Index };

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
    typer: *Typer,
    receiver_node: Node.Index,
    place: Place,
    self_type: Pool.Index,
    fn_name: []const u8,
) Allocator.Error!?Ref {
    const comp = typer.comp;
    assert(place.type != .poison);
    if (place.type == self_type) return try Place.placeValue(typer, place);

    const place_key = comp.pool.keyOf(place.type);
    switch (comp.pool.keyOf(self_type)) {
        .type_pointer => |wanted| {
            if (place_key == .type_pointer and place_key.type_pointer.child == wanted.child) {
                if (wanted.mutable and place_key.type_pointer.mutable == false) {
                    try typer.fail(receiver_node, .{
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
                return try Place.placeValue(typer, place);
            }
            if (place.type == wanted.child) {
                if (wanted.mutable) {
                    if (place.immutable) |why| {
                        try reportReceiverImmutable(typer, receiver_node, place, why, fn_name);
                        return null;
                    }
                }
                const addressed = try Place.placeAddress(typer, place) orelse return null;
                return addressed.ref;
            }
        },
        else => if (place_key == .type_pointer and place_key.type_pointer.child == self_type) {
            const pointer = try Place.placeValue(typer, place);
            return try typer.emitOne(receiver_node, .load, self_type, pointer);
        },
    }
    try typer.fail(receiver_node, .{
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
    typer: *Typer,
    node: Node.Index,
    place: Place,
    why: Place.Reason,
    fn_name: []const u8,
) Allocator.Error!void {
    const what: []const u8 = switch (why) {
        .let_bound => "was bound with 'let'",
        .param_bound => "is a parameter, a copy that dies with the call",
        .read_only => |crossed| try typer.comp.fmt("sits behind a '{s}', which is read-only", .{
            try typer.comp.typeName(try Place.crossedType(typer, crossed, false)),
        }),
        .temporary => "is a temporary that no one else can see",
    };
    try typer.fail(node, .{
        .code = .not_assignable,
        .message = try typer.comp.fmt("'{s}' writes through its receiver, and '{s}' {s}", .{
            fn_name, place.root_name, what,
        }),
        .label = "immutable receiver",
        .help = "bind it with 'var' to let a method change it",
    });
}

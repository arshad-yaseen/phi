//! The operations the compiler performs itself, reached as `@name`.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Layout = @import("Layout.zig");
const Pool = @import("Pool.zig");
const Token = @import("Token.zig");
const spell = @import("util/spell.zig");

const Node = AST.Node;
const Value = Check.Value;

/// Spelled in source exactly as the tag is written, after the `@`.
pub const Builtin = enum {
    /// `@ptr_cast[T](pointer)`, retyping a pointer without moving it.
    ptr_cast,
    /// `@int_cast[T](n)`, the number where `T` holds it, and `none` where it does not.
    int_cast,
    /// `@size_of[T]()`, the bytes a value of `T` occupies, a constant.
    size_of,
    /// `@align_of[T]()`, the alignment a value of `T` requires, a constant.
    align_of,
    /// `@min_int[T]()`, the lowest value the integer type `T` holds, a constant.
    min_int,
    /// `@max_int[T]()`, the highest value the integer type `T` holds, a constant.
    max_int,
    /// `@fill(v)`, an array whose every element is `v`.
    fill,
    /// `@trap()`, stopping the program where it stands.
    trap,

    /// Validated before typing a call. Type rules live with the case that needs them.
    pub const Shape = struct {
        /// Below `types_max` where the result names the type, so a hint can pin it.
        types_min: u8,
        types_max: u8,
        args: u8,
    };

    pub fn shape(builtin: Builtin) Shape {
        return switch (builtin) {
            .ptr_cast => .{ .types_min = 1, .types_max = 1, .args = 1 },
            .int_cast => .{ .types_min = 0, .types_max = 1, .args = 1 },
            .fill => .{ .types_min = 0, .types_max = 0, .args = 1 },
            .size_of, .align_of, .min_int, .max_int => .{
                .types_min = 1,
                .types_max = 1,
                .args = 0,
            },
            .trap => .{ .types_min = 0, .types_max = 0, .args = 0 },
        };
    }

    /// Std-only is the price of being able to break a guarantee the checker made.
    pub fn stdOnly(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast => true,
            .int_cast, .size_of, .align_of, .min_int, .max_int, .fill, .trap => false,
        };
    }

    /// The name a `@name` token spells, without the sigil that opened it.
    pub fn nameOf(text: []const u8) []const u8 {
        assert(text.len > 1);
        assert(text[0] == '@');
        return text[1..];
    }

    pub fn fromName(text: []const u8) ?Builtin {
        assert(text.len > 0);
        return std.meta.stringToEnum(Builtin, text);
    }

    /// For a suggestion when a name is missed.
    pub const names = std.meta.fieldNames(Builtin);

    /// The widest the table goes, so no call site has to check its buffers.
    pub const types_max = blk: {
        var most: u8 = 0;
        for (std.enums.values(Builtin)) |builtin| most = @max(most, builtin.shape().types_max);
        break :blk most;
    };

    pub const args_max = blk: {
        var most: u8 = 0;
        for (std.enums.values(Builtin)) |builtin| most = @max(most, builtin.shape().args);
        break :blk most;
    };

    /// The builtin a `@name` spells, and whether this file may reach it. Null once reported.
    pub fn resolve(check: *Check, name_token: Token.Index) Allocator.Error!?Builtin {
        const comp = check.comp;
        const name_text = Builtin.nameOf(check.tree.tokenSlice(name_token));

        const which = Builtin.fromName(name_text) orelse {
            try check.failToken(name_token, .{
                .code = .no_such_member,
                .message = try comp.fmt("there is no builtin named '@{s}'", .{name_text}),
                .label = "no such builtin",
                .help = try suggest(check, name_text),
            });
            return null;
        };
        if (which.stdOnly() and check.module.space != .std) {
            try check.failToken(name_token, .{
                .code = .builtin_outside_std,
                .message = try comp.fmt("only the standard library reaches '@{s}'", .{name_text}),
                .label = "not available here",
                .help = "std wraps it in an ordinary declaration, so call that instead",
            });
            return null;
        }
        return which;
    }

    /// A builtin stands only in a call, so a bare `@name` is a mistake.
    pub fn notAValue(check: *Check, node: Node.Index) Allocator.Error!Value {
        try check.fail(node, .{
            .code = .not_a_function,
            .message = "a builtin is not a value, so call it",
            .label = "missing the call",
            .help = "write '@name(...)', with its type arguments if it takes any",
        });
        return .poison;
    }

    /// Arity from the table, then the one case that knows what this builtin means.
    pub fn call(
        builtin: Builtin,
        check: *Check,
        node: Node.Index,
        type_args: []const Node.Index,
        args: []const Node.Index,
        hint: ?Pool.Index,
    ) Allocator.Error!Value {
        const comp = check.comp;
        const form = builtin.shape();

        if (args.len != form.args) {
            try check.fail(node, .{
                .code = .wrong_arity,
                .message = try comp.fmt("'@{s}' takes {d} argument{s}, and this call has {d}", .{
                    @tagName(builtin), form.args, Check.plural(form.args), args.len,
                }),
                .label = "wrong number of arguments",
            });
            return .poison;
        }

        var types: [types_max]Pool.Index = undefined;
        if (try resolveTypes(check, node, builtin, type_args, &types) == false) return .poison;

        var values: [args_max]Value = undefined;
        for (args, 0..) |argument, position| {
            const value = try check.checkExpr(argument, null);
            if (value == .diverged) return .diverged;
            if (try check.valueOnly(argument, value) == false) return .poison;
            if (value == .poison) return .poison;
            values[position] = value;
        }

        switch (builtin) {
            .ptr_cast => return ptrCast(check, args[0], types[0], values[0]),
            .int_cast => {
                const written: ?Pool.Index = if (type_args.len == 1) types[0] else null;
                const wanted = try intCastDestination(check, node, written, hint) orelse
                    return .poison;
                return intCast(check, node, args[0], wanted, values[0]);
            },
            .size_of, .align_of => return layoutOf(check, node, builtin, types[0]),
            .min_int, .max_int => return limitOf(check, node, builtin, types[0]),
            .fill => {
                const wanted = try fillDestination(check, node, hint) orelse return .poison;
                return fill(check, node, args[0], wanted, values[0]);
            },
            .trap => {
                try check.trap();
                return .diverged;
            },
        }
    }
};

fn suggest(check: *Check, text: []const u8) Allocator.Error!?[]const u8 {
    var closest: spell.Closest = .{ .target = text };
    for (Builtin.names) |candidate| closest.consider(candidate);
    return check.comp.didYouMean(closest);
}

/// The type arguments as written, within the count the table allows. False once reported.
fn resolveTypes(
    check: *Check,
    node: Node.Index,
    builtin: Builtin,
    written: []const Node.Index,
    out: *[Builtin.types_max]Pool.Index,
) Allocator.Error!bool {
    const comp = check.comp;
    const form = builtin.shape();
    assert(form.types_max <= out.len);

    if (written.len < form.types_min or written.len > form.types_max) {
        const bound: []const u8 = if (form.types_min < form.types_max) "at most " else "";
        try check.fail(node, .{
            .code = .generic_arguments,
            .message = try comp.fmt("'@{s}' takes {s}{d} type argument{s}, and this writes {d}", .{
                @tagName(builtin),
                bound,
                form.types_max,
                Check.plural(form.types_max),
                written.len,
            }),
            .label = "wrong number of type arguments",
        });
        return false;
    }

    for (written, 0..) |type_arg, position| {
        const resolved = try check.resolveWrittenType(type_arg);
        if (resolved == .poison) return false;
        out[position] = resolved;
    }
    return true;
}

/// The type `@int_cast` converts to. Its result leads with the destination, so a
/// landing names it whole or as its first member. Null once reported.
fn intCastDestination(
    check: *Check,
    node: Node.Index,
    written: ?Pool.Index,
    hint: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    const comp = check.comp;

    if (written) |wanted| {
        if (Pool.isSizedInt(wanted)) return wanted;
        try failDestination(check, node, wanted, "and this is");
        return null;
    }

    const landing = comp.pool.firstMember(hint orelse .void_type);
    if (Pool.isSizedInt(landing)) return landing;

    // a type that cannot be the destination is not the same as no type at all
    if (check.typeCanHold(landing)) {
        try failDestination(check, node, landing, "and this lands on");
        return null;
    }
    try check.fail(node, .{
        .code = .inference_failed,
        .message = "nothing here says what type '@int_cast' converts to",
        .label = "no type in sight",
        .help = "write it, as in '@int_cast[u8](n)', or annotate what the call feeds",
    });
    return null;
}

fn failDestination(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    reached: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'@int_cast' converts between integers, {s} {s}", .{
            reached,
            try check.comp.typeName(found),
        }),
        .label = "not an integer type",
    });
}

/// The number where the type holds it, and `none` where it does not.
fn intCast(
    check: *Check,
    node: Node.Index,
    operand_node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(Pool.isSizedInt(wanted));

    const found = check.typeOf(operand);
    if (Pool.isInteger(found) == false) {
        try check.fail(operand_node, .{
            .code = .bad_operand,
            .message = try comp.fmt("'@int_cast' converts a number, and this is {s}", .{
                try comp.typeName(found),
            }),
            .label = "not a number",
        });
        return .poison;
    }

    const absent = try check.noneType(node);
    if (absent == .poison) return .poison;
    const result = switch (try comp.pool.unite(comp.gpa, &.{ wanted, absent })) {
        .index => |index| index,
        // an integer type is never `none`, and two members are never too wide
        .duplicate, .too_wide => unreachable,
    };

    if (operand == .constant) {
        assert(comp.pool.keyOf(operand.constant) == .value_int);
        const written = comp.pool.keyOf(operand.constant).value_int.value;
        const member = if (Pool.fitsInt(written, wanted))
            try comp.pool.intern(comp.gpa, .{ .value_int = .{ .type = wanted, .value = written } })
        else
            try comp.pool.intern(comp.gpa, .{ .value_unit = absent });
        return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_union = .{ .type = result, .value = member },
        }) };
    }

    const ref = try check.emitOne(node, .int_cast, result, Check.refOf(operand));
    return Check.runtimeValue(ref, result);
}

/// The array `@fill` builds. Null once reported.
fn fillDestination(
    check: *Check,
    node: Node.Index,
    hint: ?Pool.Index,
) Allocator.Error!?Pool.Index {
    const comp = check.comp;

    const landing = comp.pool.firstMember(hint orelse .void_type);
    if (comp.pool.keyOf(landing) == .type_array) return landing;

    if (check.typeCanHold(landing)) {
        try failFillDestination(check, node, landing);
        return null;
    }
    try check.fail(node, .{
        .code = .inference_failed,
        .message = "nothing here says what array '@fill' builds",
        .label = "no type in sight",
        .help = "annotate what it feeds, as in 'var buffer: [20]u8 = @fill(0)'",
    });
    return null;
}

fn failFillDestination(check: *Check, node: Node.Index, found: Pool.Index) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("'@fill' builds an array, and this lands on {s}", .{
            try check.comp.typeName(found),
        }),
        .label = "not an array type",
    });
}

fn fill(
    check: *Check,
    node: Node.Index,
    operand_node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    if (operand != .constant) {
        try check.fail(operand_node, .{
            .code = .not_constant,
            .message = "'@fill' repeats a constant, and this is settled at run time",
            .label = "not a constant",
            .help = "write a loop to fill storage with something worked out as it runs",
        });
        return .poison;
    }

    const filled = try fillArray(check, node, wanted, operand.constant, 0) orelse return .poison;
    return .{ .constant = filled };
}

fn fillArray(
    check: *Check,
    node: Node.Index,
    wanted: Pool.Index,
    value: Pool.Index,
    depth: u32,
) Allocator.Error!?Pool.Index {
    const comp = check.comp;
    // a written type nests no deeper than the parser allows
    assert(depth < AST.nest_max);

    const array = comp.pool.keyOf(wanted).type_array;
    const element: Pool.Index = element: {
        if (comp.pool.keyOf(array.child) == .type_array) {
            break :element try fillArray(check, node, array.child, value, depth + 1) orelse
                return null;
        }
        switch (try comp.pool.fit(comp.gpa, value, array.child)) {
            .value => |fitted| break :element fitted,
            .does_not_fit, .wrong_kind => {
                try check.fail(node, .{
                    .code = .does_not_fit,
                    .message = try comp.fmt("{s} does not fit in {s}, which is what '{s}' holds", .{
                        try comp.spellValue(value),
                        try comp.typeName(array.child),
                        try comp.typeName(wanted),
                    }),
                    .label = "the wrong element",
                });
                return null;
            },
        }
    };

    if (array.len == 0) {
        return try comp.pool.intern(comp.gpa, .{
            .value_aggregate = .{ .type = wanted, .elems = &.{} },
        });
    }
    return try comp.pool.intern(comp.gpa, .{
        .value_splat = .{ .type = wanted, .element = element },
    });
}

/// A size or an alignment, an untyped constant, so it meets any integer.
fn layoutOf(
    check: *Check,
    node: Node.Index,
    builtin: Builtin,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(builtin == .size_of or builtin == .align_of);

    const layout = Layout.of(comp, check.origin(node), wanted) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Poison => return .poison,
        error.TooLarge => {
            try check.fail(node, .{
                .code = .type_too_large,
                .message = try comp.fmt("'{s}' is larger than the 4 GiB a type may hold", .{
                    try comp.typeName(wanted),
                }),
                .label = "too large",
            });
            return .poison;
        },
    };

    const answer: u32 = if (builtin == .size_of) layout.size else layout.alignment;
    return .{ .constant = try comp.pool.intern(comp.gpa, .{
        .value_int = .{ .type = .untyped_int_type, .value = answer },
    }) };
}

/// An edge of an integer type, an untyped constant, so it meets any type it fits.
fn limitOf(
    check: *Check,
    node: Node.Index,
    builtin: Builtin,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(builtin == .min_int or builtin == .max_int);

    if (Pool.isInteger(wanted) == false) {
        try check.fail(node, .{
            .code = .bad_operand,
            .message = try comp.fmt("'@{s}' needs an integer type, and this is {s}", .{
                @tagName(builtin), try comp.typeName(wanted),
            }),
            .label = "not an integer type",
            .help = "the integer types are 'i8' through 'i64' and 'u8' through 'u64'",
        });
        return .poison;
    }

    const edge = if (builtin == .min_int) Pool.minInt(wanted) else Pool.maxInt(wanted);
    return .{ .constant = try comp.pool.intern(comp.gpa, .{
        .value_int = .{ .type = .untyped_int_type, .value = edge },
    }) };
}

/// Retypes the pointee and keeps what the pointer may do.
fn ptrCast(
    check: *Check,
    node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const found = check.typeOf(operand);

    const pointer = try check.pointerAt(node, found, "@ptr_cast", null) orelse return .poison;

    const result = try check.pointerTo(wanted, pointer.mutable);
    const ref = try check.emitOne(node, .ptr_cast, result, Check.refOf(operand));
    return Check.runtimeValue(ref, result);
}

comptime {
    assert(@typeInfo(Builtin).@"enum".fields.len > 0);
    for (std.enums.values(Builtin)) |builtin| {
        assert(builtin.shape().types_min <= builtin.shape().types_max);
    }
}

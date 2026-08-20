const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("AST.zig");
const Check = @import("Check.zig");
const Compilation = @import("Compilation.zig");
const Diagnostic = @import("Diagnostic.zig");
const Layout = @import("Layout.zig");
const Pool = @import("Pool.zig");
const Target = @import("Target.zig");
const Token = @import("Token.zig");

const Closest = Compilation.Closest;
const Node = AST.Node;
const Value = Check.Value;

pub const Builtin = enum {
    ptr_cast,
    view,
    int_from_ptr,
    int_cast,
    size_of,
    align_of,
    min_int,
    max_int,
    target_os,
    target_arch,
    repeat,
    trap,

    pub const Shape = struct {
        types_min: u8,
        types_max: u8,
        args: u8,
    };

    pub fn shape(builtin: Builtin) Shape {
        return switch (builtin) {
            .ptr_cast => .{ .types_min = 1, .types_max = 1, .args = 1 },
            .view => .{ .types_min = 0, .types_max = 0, .args = 2 },
            .int_from_ptr => .{ .types_min = 0, .types_max = 0, .args = 1 },
            .int_cast => .{ .types_min = 0, .types_max = 1, .args = 1 },
            .repeat => .{ .types_min = 0, .types_max = 0, .args = 1 },
            .size_of, .align_of, .min_int, .max_int => .{
                .types_min = 1,
                .types_max = 1,
                .args = 0,
            },
            .target_os, .target_arch, .trap => .{ .types_min = 0, .types_max = 0, .args = 0 },
        };
    }

    /// Std-only is the price of being able to break a guarantee the checker made.
    pub fn stdOnly(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast, .view, .int_from_ptr => true,
            .int_cast, .size_of, .align_of, .min_int, .max_int, .repeat, .trap => false,
            .target_os, .target_arch => false,
        };
    }

    pub fn needsBody(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast, .view, .int_from_ptr, .trap => true,
            .int_cast, .size_of, .align_of, .min_int, .max_int, .repeat => false,
            .target_os, .target_arch => false,
        };
    }

    pub fn nameOf(text: []const u8) []const u8 {
        assert(text.len > 1);
        assert(text[0] == '@');
        return text[1..];
    }

    pub fn fromName(text: []const u8) ?Builtin {
        assert(text.len > 0);
        return std.meta.stringToEnum(Builtin, text);
    }

    pub const names = std.meta.fieldNames(Builtin);

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

    pub fn notAValue(check: *Check, node: Node.Index) Allocator.Error!Value {
        return check.refuse(node, .{
            .code = .not_a_function,
            .message = "a builtin is not a value, so call it",
            .label = "missing the call",
            .help = "write '@name(...)', with its type arguments if it takes any",
        });
    }

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
            const name = try comp.fmt("@{s}", .{@tagName(builtin)});
            try check.failArity(node, name, form.args, args.len, &.{});
            return .poison;
        }

        var types: [types_max]Pool.Index = undefined;
        if (try resolveTypes(check, node, builtin, type_args, &types) == false) return .poison;

        var values: [args_max]Value = undefined;
        for (args, 0..) |argument, position| {
            values[position] = try check.checkValue(argument, null);
            if (values[position].stops()) return values[position];
        }

        switch (builtin) {
            .ptr_cast => return ptrCast(check, args[0], types[0], values[0]),
            .view => return view(check, node, args, values[0..2]),
            .int_from_ptr => return intFromPtr(check, node, args[0], values[0]),
            .int_cast => {
                const written: ?Pool.Index = if (type_args.len == 1) types[0] else null;
                const wanted = try destination(check, node, written, hint, int_cast_wants) orelse
                    return .poison;
                return intCast(check, node, args[0], wanted, values[0]);
            },
            .size_of, .align_of => return layoutOf(check, node, builtin, types[0]),
            .min_int, .max_int => return limitOf(check, node, builtin, types[0]),
            .target_os => return targetMember(
                check,
                node,
                hint,
                target_os_wants,
                @tagName(comp.target.os),
            ),
            .target_arch => return targetMember(
                check,
                node,
                hint,
                target_arch_wants,
                @tagName(comp.target.arch),
            ),
            .repeat => {
                const wanted = try destination(check, node, null, hint, repeat_wants) orelse
                    return .poison;
                return repeat(check, node, args[0], wanted, values[0]);
            },
            .trap => {
                try check.trap();
                return .diverged;
            },
        }
    }
};

fn suggest(check: *Check, text: []const u8) Allocator.Error!?[]const u8 {
    var closest: Closest = .{ .target = text };
    for (Builtin.names) |candidate| closest.consider(candidate);
    return check.comp.didYouMean(closest);
}

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

const Destination = struct {
    shape: enum { integer, array, set },
    does: []const u8,
    label: []const u8,
    missing: []const u8,
    help: []const u8,

    fn accepts(wants: Destination, pool: *const Pool, index: Pool.Index) bool {
        return switch (wants.shape) {
            .integer => Pool.isSizedInt(index),
            .array => pool.keyOf(index) == .type_array,
            .set => pool.isUnion(index),
        };
    }
};

const int_cast_wants: Destination = .{
    .shape = .integer,
    .does = "'@int_cast' converts between integers",
    .label = "not an integer type",
    .missing = "nothing here says what type '@int_cast' converts to",
    .help = "write it, as in '@int_cast[u8](n)', or annotate what the call feeds",
};

fn targetWants(comptime name: []const u8, comptime example: []const u8) Destination {
    return .{
        .shape = .set,
        .does = "'@" ++ name ++ "' answers a member of a union",
        .label = "not a union",
        .missing = "nothing here says which union '@" ++ name ++ "' lands on",
        .help = "annotate what it feeds, as in '" ++ example ++ " = @" ++ name ++ "()'",
    };
}

const target_os_wants: Destination = targetWants("target_os", "let os: Os");

const target_arch_wants: Destination = targetWants("target_arch", "let arch: Arch");

const repeat_wants: Destination = .{
    .shape = .array,
    .does = "'@repeat' builds an array",
    .label = "not an array type",
    .missing = "nothing here says what array '@repeat' builds",
    .help = "annotate what it feeds, as in 'var buffer: [20]u8 = @repeat(0)'",
};

fn destination(
    check: *Check,
    node: Node.Index,
    written: ?Pool.Index,
    hint: ?Pool.Index,
    wants: Destination,
) Allocator.Error!?Pool.Index {
    const comp = check.comp;
    if (written) |wanted| {
        if (wants.accepts(&comp.pool, wanted)) return wanted;
        try failDestination(check, node, wanted, wants, "and this is");
        return null;
    }

    const wanted = hint orelse .void_type;
    if (wants.accepts(&comp.pool, wanted)) return wanted;

    // a union otherwise lands on its first member, the way a value entering it does
    const landing = comp.pool.firstMember(wanted);
    if (wants.accepts(&comp.pool, landing)) return landing;

    // a type that cannot be the destination is not the same as no type at all
    if (check.typeCanHold(landing)) {
        try failDestination(check, node, landing, wants, "and this lands on");
        return null;
    }
    try check.fail(node, .{
        .code = .inference_failed,
        .message = wants.missing,
        .label = "no type in sight",
        .help = wants.help,
    });
    return null;
}

fn failDestination(
    check: *Check,
    node: Node.Index,
    found: Pool.Index,
    wants: Destination,
    reached: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try check.fail(node, .{
        .code = .bad_operand,
        .message = try check.comp.fmt("{s}, {s} {s}", .{
            wants.does,
            reached,
            try check.comp.typeName(found),
        }),
        .label = wants.label,
    });
}

/// The member of the landing union the target spells. The library names the
/// members and the compiler only picks one, so there is one vocabulary.
fn targetMember(
    check: *Check,
    node: Node.Index,
    hint: ?Pool.Index,
    wants: Destination,
    spelled: []const u8,
) Allocator.Error!Value {
    const comp = check.comp;
    const wanted = try destination(check, node, null, hint, wants) orelse return .poison;

    var members = comp.pool.membersOf(wanted);
    while (members.next()) |member| {
        const named = switch (comp.pool.keyOf(member)) {
            .type_unit => |decl| decl,
            else => continue,
        };
        if (comp.pool.sameText(comp.declAt(named).name, spelled) == false) continue;

        const held = try comp.pool.intern(comp.gpa, .{ .value_unit = member });
        return .{ .constant = try comp.pool.intern(comp.gpa, .{
            .value_union = .{ .type = wanted, .value = held },
        }) };
    }

    return check.refuse(node, .{
        .code = .not_a_member,
        .message = try comp.fmt("this build targets '{s}', and {s} has no member named '{s}'", .{
            spelled,
            try comp.typeName(wanted),
            spelled,
        }),
        .label = "no member for this target",
        .help = try comp.fmt("declare 'type {s}' and list it among the members", .{spelled}),
    });
}

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
        return check.refuse(operand_node, .{
            .code = .bad_operand,
            .message = try comp.fmt("'@int_cast' converts a number, and this is {s}", .{
                try comp.typeName(found),
            }),
            .label = "not a number",
        });
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

    return check.emitOneValue(node, .int_cast, result, Check.refOf(operand));
}

fn repeat(
    check: *Check,
    node: Node.Index,
    operand_node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    if (operand != .constant) {
        return check.refuse(operand_node, .{
            .code = .not_constant,
            .message = "'@repeat' takes a constant, and this is settled at run time",
            .label = "not a constant",
            .help = "write a loop to fill storage with something worked out as it runs",
        });
    }

    const repeated = try repeatArray(check, node, wanted, operand.constant, 0) orelse
        return .poison;
    return .{ .constant = repeated };
}

fn repeatArray(
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
            break :element try repeatArray(check, node, array.child, value, depth + 1) orelse
                return null;
        }
        switch (try comp.pool.fit(comp.gpa, value, array.child, .allowed)) {
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
        .value_repeat = .{ .type = wanted, .element = element },
    });
}

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
            return check.refuse(node, .{
                .code = .type_too_large,
                .message = try comp.fmt("'{s}' is larger than the 4 GiB a type may hold", .{
                    try comp.typeName(wanted),
                }),
                .label = "too large",
            });
        },
    };

    return check.untypedInt(if (builtin == .size_of) layout.size else layout.alignment);
}

fn limitOf(
    check: *Check,
    node: Node.Index,
    builtin: Builtin,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(builtin == .min_int or builtin == .max_int);

    if (Pool.isInteger(wanted) == false) {
        return check.refuse(node, .{
            .code = .bad_operand,
            .message = try comp.fmt("'@{s}' needs an integer type, and this is {s}", .{
                @tagName(builtin), try comp.typeName(wanted),
            }),
            .label = "not an integer type",
            .help = "the integer types are 'i8' through 'i64' and 'u8' through 'u64'",
        });
    }

    return check.untypedInt(if (builtin == .min_int) Pool.minInt(wanted) else Pool.maxInt(wanted));
}

fn ptrCast(
    check: *Check,
    node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const found = check.typeOf(operand);
    const pointer = try check.pointerAt(node, found, "@ptr_cast", null) orelse return .poison;
    const result = try check.pointerTo(wanted, pointer.mutable);
    return check.emitOneValue(node, .ptr_cast, result, Check.refOf(operand));
}

/// A view of `count` elements at a pointer, as writable as the pointer.
fn view(
    check: *Check,
    node: Node.Index,
    args: []const Node.Index,
    values: []const Value,
) Allocator.Error!Value {
    const comp = check.comp;
    assert(args.len == 2);
    assert(values.len == 2);

    const found = check.typeOf(values[0]);
    const pointer = try check.pointerAt(args[0], found, "@view", null) orelse return .poison;

    const count_type = check.typeOf(values[1]);
    if (Pool.isInteger(count_type) == false) {
        return check.refuse(args[1], .{
            .code = .bad_operand,
            .message = try comp.fmt("'@view' takes a count, and this is {s}", .{
                try comp.typeName(count_type),
            }),
            .label = "not a count",
            .help = "a count is a 'u64', the way a view's own '.len' is",
        });
    }
    const count = try check.coerce(values[1], .u64_type, args[1]);
    if (count == .poison) return .poison;

    const result = try check.sliceOf(pointer.child, pointer.mutable);
    return check.emitValue(node, .slice_from, result, .{
        .bin = .{ .lhs = Check.refOf(values[0]), .rhs = Check.refOf(count) },
    });
}

fn intFromPtr(
    check: *Check,
    node: Node.Index,
    operand_node: Node.Index,
    operand: Value,
) Allocator.Error!Value {
    const found = check.typeOf(operand);
    _ = try check.pointerAt(operand_node, found, "@int_from_ptr", null) orelse return .poison;
    return check.emitOneValue(node, .int_from_ptr, .u64_type, Check.refOf(operand));
}

comptime {
    assert(@typeInfo(Builtin).@"enum".fields.len > 0);
    for (std.enums.values(Builtin)) |builtin| {
        assert(builtin.shape().types_min <= builtin.shape().types_max);
    }
}

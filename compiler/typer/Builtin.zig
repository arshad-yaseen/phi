const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const AST = @import("../AST.zig");
const Typer = @import("../Typer.zig");
const Diagnostic = @import("../Diagnostic.zig");
const Layout = @import("../Layout.zig");
const Literal = @import("../Literal.zig");
const Pool = @import("../Pool.zig");
const Token = @import("../Token.zig");
const Resolve = @import("Resolve.zig");
const Expr = @import("Expr.zig");

const Closest = Diagnostic.Closest;
const Node = AST.Node;
const Value = Typer.Value;

pub const Builtin = enum {
    ptr_cast,
    view,
    int_from_ptr,
    int_cast,
    int_fits,
    size_of,
    align_of,
    min_int,
    max_int,
    target_os,
    target_arch,
    repeat,
    trap,
    compile_error,

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
            .int_cast, .int_fits => .{ .types_min = 0, .types_max = 1, .args = 1 },
            .repeat => .{ .types_min = 0, .types_max = 0, .args = 1 },
            .size_of, .align_of, .min_int, .max_int => .{
                .types_min = 1,
                .types_max = 1,
                .args = 0,
            },
            .target_os, .target_arch, .trap => .{ .types_min = 0, .types_max = 0, .args = 0 },
            .compile_error => .{ .types_min = 0, .types_max = 0, .args = 1 },
        };
    }

    pub fn stdOnly(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast, .view, .int_from_ptr => true,
            .int_cast, .int_fits, .size_of, .align_of, .min_int, .max_int => false,
            .repeat, .trap, .target_os, .target_arch, .compile_error => false,
        };
    }

    pub fn needsBody(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast, .view, .int_from_ptr, .trap => true,
            .int_cast, .int_fits, .size_of, .align_of, .min_int, .max_int, .repeat => false,
            .target_os, .target_arch, .compile_error => false,
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

    pub fn resolve(typer: *Typer, name_token: Token.Index) Allocator.Error!?Builtin {
        const comp = typer.comp;
        const name_text = Builtin.nameOf(typer.tree.tokenSlice(name_token));

        const which = Builtin.fromName(name_text) orelse {
            try typer.failToken(name_token, .{
                .code = .no_such_member,
                .message = try comp.fmt("there is no builtin named '@{s}'", .{name_text}),
                .label = "no such builtin",
                .help = try suggest(typer, name_text),
            });
            return null;
        };
        if (which.stdOnly() and typer.module.space != .std) {
            try typer.failToken(name_token, .{
                .code = .builtin_outside_std,
                .message = try comp.fmt("only the standard library reaches '@{s}'", .{name_text}),
                .label = "not available here",
                .help = "std wraps it in an ordinary declaration, so call that instead",
            });
            return null;
        }
        return which;
    }

    pub fn notAValue(typer: *Typer, node: Node.Index) Allocator.Error!Value {
        return typer.refuse(node, .{
            .code = .not_a_function,
            .message = "a builtin is not a value, so call it",
            .label = "missing the call",
            .help = "write '@name(...)', with its type arguments if it takes any",
        });
    }

    pub fn call(
        builtin: Builtin,
        typer: *Typer,
        node: Node.Index,
        type_args: []const Node.Index,
        args: []const Node.Index,
        hint: ?Pool.Index,
    ) Allocator.Error!Value {
        const comp = typer.comp;
        const form = builtin.shape();

        if (args.len != form.args) {
            const name = try comp.fmt("@{s}", .{@tagName(builtin)});
            try typer.failArity(node, name, .value, form.args, args.len, &.{});
            return .poison;
        }

        var types: [types_max]Pool.Index = undefined;
        if (try resolveTypes(typer, node, builtin, type_args, &types) == false) return .poison;

        var values: [args_max]Value = undefined;
        for (args, 0..) |argument, position| {
            values[position] = try typer.checkValue(argument, null);
            if (values[position].stops()) return values[position];
        }

        switch (builtin) {
            .ptr_cast => return ptrCast(typer, args[0], types[0], values[0]),
            .view => return view(typer, node, args, values[0..2]),
            .int_from_ptr => return intFromPtr(typer, node, args[0], values[0]),
            .int_cast, .int_fits => {
                const written: ?Pool.Index = if (type_args.len == 1) types[0] else null;
                const wants = if (builtin == .int_cast) int_cast_wants else int_fits_wants;
                const wanted = try destination(typer, node, written, hint, wants) orelse
                    return .poison;
                const found = typer.typeOf(values[0]);
                if (Pool.isInteger(found) == false) return typer.refuse(args[0], .{
                    .code = .bad_operand,
                    .message = try comp.fmt("'@{t}' converts a number, and this is {s}", .{
                        builtin, try comp.typeName(found),
                    }),
                    .label = "not a number",
                });
                if (builtin == .int_cast) return intCast(typer, node, args[0], wanted, values[0]);
                return intFits(typer, node, wanted, values[0]);
            },
            .size_of, .align_of => return layoutOf(typer, node, builtin, types[0]),
            .min_int, .max_int => return limitOf(typer, node, builtin, types[0]),
            .target_os => return targetMember(
                typer,
                node,
                hint,
                target_os_wants,
                @tagName(comp.options.target.os()),
            ),
            .target_arch => return targetMember(
                typer,
                node,
                hint,
                target_arch_wants,
                @tagName(comp.options.target.arch()),
            ),
            .repeat => {
                const wanted = try destination(typer, node, null, hint, repeat_wants) orelse
                    return .poison;
                return repeat(typer, node, args[0], wanted, values[0]);
            },
            .trap => {
                try typer.trap();
                return .diverged;
            },
            .compile_error => return compileError(typer, node, args[0]),
        }
    }
};

fn compileError(typer: *Typer, node: Node.Index, message: Node.Index) Allocator.Error!Value {
    const said = try messageText(typer, message) orelse return typer.refuse(message, .{
        .code = .compile_error,
        .message = "'@compile_error' says why in a string written at the call",
        .label = "no reason here",
        .help = "give one, as in '@compile_error(\"no pages on this target\")'",
    });
    try typer.fail(node, .{
        .code = .compile_error,
        .message = said,
        .label = "the program refuses this build",
    });
    if (typer.builder == null) return .poison;
    try typer.trap();
    return .diverged;
}

fn messageText(typer: *Typer, node: Node.Index) Allocator.Error!?[]const u8 {
    if (typer.tree.nodeTag(node) != .string_literal) return null;

    var out: std.ArrayList(u8) = .empty;
    var reading = Literal.bytesOf(typer.tree.tokenSlice(typer.tree.nodeMainToken(node)));
    while (reading.next()) |piece| switch (piece) {
        .bytes => |run| try out.appendSlice(typer.comp.arena.allocator(), run),
        .refused => return null,
    };
    if (out.items.len == 0) return null;
    return out.items;
}

fn suggest(typer: *Typer, text: []const u8) Allocator.Error!?[]const u8 {
    var closest: Closest = .{ .target = text };
    for (Builtin.names) |candidate| closest.consider(candidate);
    return closest.didYouMean(typer.comp.arena.allocator());
}

fn resolveTypes(
    typer: *Typer,
    node: Node.Index,
    builtin: Builtin,
    written: []const Node.Index,
    out: *[Builtin.types_max]Pool.Index,
) Allocator.Error!bool {
    const comp = typer.comp;
    const form = builtin.shape();
    assert(form.types_max <= out.len);

    if (written.len < form.types_min or written.len > form.types_max) {
        const bound: []const u8 = if (form.types_min < form.types_max) "at most " else "";
        try typer.fail(node, .{
            .code = .generic_arguments,
            .message = try comp.fmt("'@{s}' takes {s}{d} type argument{s}, and this writes {d}", .{
                @tagName(builtin),
                bound,
                form.types_max,
                Typer.plural(form.types_max),
                written.len,
            }),
            .label = "wrong number of type arguments",
        });
        return false;
    }

    for (written, 0..) |type_arg, position| {
        const resolved = try Resolve.resolveWrittenType(typer, type_arg);
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

const int_cast_wants: Destination = convertWants("int_cast");
const int_fits_wants: Destination = convertWants("int_fits");

fn convertWants(comptime name: []const u8) Destination {
    return .{
        .shape = .integer,
        .does = "'@" ++ name ++ "' converts between integers",
        .label = "not an integer type",
        .missing = "nothing here says what type '@" ++ name ++ "' converts to",
        .help = "write it, as in '@" ++ name ++ "[u8](n)', or annotate what the call feeds",
    };
}

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
    typer: *Typer,
    node: Node.Index,
    written: ?Pool.Index,
    hint: ?Pool.Index,
    wants: Destination,
) Allocator.Error!?Pool.Index {
    const comp = typer.comp;
    if (written) |wanted| {
        if (wants.accepts(&comp.pool, wanted)) return wanted;
        try failDestination(typer, node, wanted, wants, "and this is");
        return null;
    }

    const wanted = hint orelse .void_type;
    if (wants.accepts(&comp.pool, wanted)) return wanted;

    const landing = comp.pool.firstMember(wanted);
    if (wants.accepts(&comp.pool, landing)) return landing;

    if (typer.typeCanHold(landing)) {
        try failDestination(typer, node, landing, wants, "and this lands on");
        return null;
    }
    try typer.fail(node, .{
        .code = .inference_failed,
        .message = wants.missing,
        .label = "no type in sight",
        .help = wants.help,
    });
    return null;
}

fn failDestination(
    typer: *Typer,
    node: Node.Index,
    found: Pool.Index,
    wants: Destination,
    reached: []const u8,
) Allocator.Error!void {
    @branchHint(.cold);
    try typer.fail(node, .{
        .code = .bad_operand,
        .message = try typer.comp.fmt("{s}, {s} {s}", .{
            wants.does,
            reached,
            try typer.comp.typeName(found),
        }),
        .label = wants.label,
    });
}

fn targetMember(
    typer: *Typer,
    node: Node.Index,
    hint: ?Pool.Index,
    wants: Destination,
    spelled: []const u8,
) Allocator.Error!Value {
    const comp = typer.comp;
    const wanted = try destination(typer, node, null, hint, wants) orelse return .poison;

    var members = comp.pool.membersOf(wanted);
    while (members.next()) |member| {
        const named = switch (comp.pool.keyOf(member)) {
            .type_unit => |decl| decl,
            else => continue,
        };
        if (comp.pool.sameText(comp.declAt(named).name, spelled) == false) continue;
        const held = try comp.pool.unitValue(comp.gpa, member);
        return .{ .constant = try comp.pool.enter(comp.gpa, wanted, held) };
    }

    return typer.refuse(node, .{
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
    typer: *Typer,
    node: Node.Index,
    operand_node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const comp = typer.comp;
    assert(Pool.isSizedInt(wanted));
    if (operand != .constant) {
        return typer.emitOneValue(node, .int_cast, wanted, Typer.refOf(operand));
    }
    const cast = try comp.pool.castInt(comp.gpa, operand.constant, wanted) orelse {
        return typer.refuse(operand_node, .{
            .code = .out_of_range,
            .message = try comp.fmt("{s} does not hold {s}", .{
                try comp.typeName(wanted),
                try comp.spellValue(operand.constant),
            }),
            .label = "does not fit",
            .help = "'@int_fits' answers 'none' where a value does not fit",
        });
    };
    return .{ .constant = cast };
}

fn intFits(
    typer: *Typer,
    node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const comp = typer.comp;
    assert(Pool.isSizedInt(wanted));
    const absent = try typer.noneType(node);
    if (absent == .poison) return .poison;
    const result = switch (try comp.pool.unite(comp.gpa, &.{ wanted, absent })) {
        .index => |index| index,
        .duplicate, .too_wide => unreachable,
    };
    if (operand != .constant) {
        return typer.emitOneValue(node, .int_fits, result, Typer.refOf(operand));
    }
    const held = try comp.pool.castInt(comp.gpa, operand.constant, wanted) orelse
        try comp.pool.unitValue(comp.gpa, absent);
    return .{ .constant = try comp.pool.enter(comp.gpa, result, held) };
}

fn repeat(
    typer: *Typer,
    node: Node.Index,
    operand_node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    if (operand != .constant) {
        return typer.refuse(operand_node, .{
            .code = .not_constant,
            .message = "'@repeat' takes a constant, and this is settled at run time",
            .label = "not a constant",
            .help = "write a loop to fill storage with something worked out as it runs",
        });
    }

    const repeated = try repeatArray(typer, node, wanted, operand.constant, 0) orelse
        return .poison;
    return .{ .constant = repeated };
}

fn repeatArray(
    typer: *Typer,
    node: Node.Index,
    wanted: Pool.Index,
    value: Pool.Index,
    depth: u32,
) Allocator.Error!?Pool.Index {
    const comp = typer.comp;
    assert(depth < AST.nest_max);

    const array = comp.pool.keyOf(wanted).type_array;
    const element: Pool.Index = element: {
        if (comp.pool.keyOf(array.child) == .type_array) {
            break :element try repeatArray(typer, node, array.child, value, depth + 1) orelse
                return null;
        }
        switch (try comp.pool.fit(comp.gpa, value, array.child, .allowed)) {
            .value => |fitted| break :element fitted,
            .does_not_fit, .wrong_kind => {
                try typer.fail(node, .{
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
    typer: *Typer,
    node: Node.Index,
    builtin: Builtin,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    assert(builtin == .size_of or builtin == .align_of);

    const layout = Layout.of(comp, typer.origin(node), wanted) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Poison => return .poison,
        error.TooLarge => {
            return typer.refuse(node, .{
                .code = .type_too_large,
                .message = try comp.fmt("'{s}' is larger than the 4 GiB a type may hold", .{
                    try comp.typeName(wanted),
                }),
                .label = "too large",
            });
        },
    };

    return typer.untypedInt(if (builtin == .size_of) layout.size else layout.alignment);
}

fn limitOf(
    typer: *Typer,
    node: Node.Index,
    builtin: Builtin,
    wanted: Pool.Index,
) Allocator.Error!Value {
    const comp = typer.comp;
    assert(builtin == .min_int or builtin == .max_int);

    if (Pool.isInteger(wanted) == false) {
        return typer.refuse(node, .{
            .code = .bad_operand,
            .message = try comp.fmt("'@{s}' needs an integer type, and this is {s}", .{
                @tagName(builtin), try comp.typeName(wanted),
            }),
            .label = "not an integer type",
            .help = "the integer types are 'i8' through 'i64' and 'u8' through 'u64'",
        });
    }

    return typer.untypedInt(if (builtin == .min_int) Pool.minInt(wanted) else Pool.maxInt(wanted));
}

fn ptrCast(
    typer: *Typer,
    node: Node.Index,
    wanted: Pool.Index,
    operand: Value,
) Allocator.Error!Value {
    const found = typer.typeOf(operand);
    const pointer = try Expr.pointerAt(typer, node, found, "@ptr_cast", null) orelse return .poison;
    const result = try typer.pointerTo(wanted, pointer.mutable);
    return typer.emitOneValue(node, .ptr_cast, result, Typer.refOf(operand));
}

fn view(
    typer: *Typer,
    node: Node.Index,
    args: []const Node.Index,
    values: []const Value,
) Allocator.Error!Value {
    const comp = typer.comp;
    assert(args.len == 2);
    assert(values.len == 2);

    const found = typer.typeOf(values[0]);
    const pointer = try Expr.pointerAt(typer, args[0], found, "@view", null) orelse return .poison;

    const count_type = typer.typeOf(values[1]);
    if (Pool.isInteger(count_type) == false) {
        return typer.refuse(args[1], .{
            .code = .bad_operand,
            .message = try comp.fmt("'@view' takes a count, and this is {s}", .{
                try comp.typeName(count_type),
            }),
            .label = "not a count",
            .help = "a count is a 'u64', the way a view's own '.len' is",
        });
    }
    const count = try typer.coerce(values[1], .u64_type, args[1]);
    if (count == .poison) return .poison;

    const result = try typer.sliceOf(pointer.child, pointer.mutable);
    return typer.emitValue(node, .slice_from, result, .{
        .bin = .{ .lhs = Typer.refOf(values[0]), .rhs = Typer.refOf(count) },
    });
}

fn intFromPtr(
    typer: *Typer,
    node: Node.Index,
    operand_node: Node.Index,
    operand: Value,
) Allocator.Error!Value {
    const found = typer.typeOf(operand);
    _ = try Expr.pointerAt(typer, operand_node, found, "@int_from_ptr", null) orelse return .poison;
    return typer.emitOneValue(node, .int_from_ptr, .u64_type, Typer.refOf(operand));
}

comptime {
    assert(@typeInfo(Builtin).@"enum".fields.len > 0);
    for (std.enums.values(Builtin)) |builtin| {
        assert(builtin.shape().types_min <= builtin.shape().types_max);
    }
}

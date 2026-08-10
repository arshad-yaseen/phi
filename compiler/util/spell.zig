//! How diagnostics and dumps spell what the tables hold.

const std = @import("std");
const assert = std.debug.assert;
const Writer = std.Io.Writer;

const Compilation = @import("../Compilation.zig");
const Pool = @import("../Pool.zig");

pub fn writeType(comp: *const Compilation, writer: *Writer, index: Pool.Index) Writer.Error!void {
    var current = index;
    var depth: u32 = 0;
    const depth_cap = 64;

    while (depth < depth_cap) : (depth += 1) {
        switch (comp.pool.keyOf(current)) {
            .type_simple => |simple| return switch (simple) {
                .poison => writer.writeAll("<broken>"),
                .untyped_int => writer.writeAll("an untyped number"),
                .untyped_float => writer.writeAll("an untyped float"),
                .untyped_aggregate => writer.writeAll("an untyped array"),
                .void => writer.writeAll("nothing"),
                else => writer.writeAll(@tagName(simple)),
            },
            .type_pointer => |pointer| {
                try writer.writeAll(if (pointer.mutable) "*var " else "*");
                current = pointer.child;
            },
            .type_array => |array| {
                try writer.print("[{d}]", .{array.len});
                current = array.child;
            },
            .type_slice => |slice| {
                try writer.writeAll(if (slice.mutable) "[]var " else "[]");
                current = slice.child;
            },
            .type_struct => |instance| return writeInstance(comp, writer, instance),
            .type_unit => |decl| {
                return writer.writeAll(comp.pool.stringText(comp.declAt(decl).name));
            },
            .type_union => |members| {
                // a member is never a union, so this recursion is one level
                for (members, 0..) |member, position| {
                    if (position > 0) try writer.writeAll(" | ");
                    try writeType(comp, writer, member);
                }
                return;
            },
            .value_int, .value_float, .value_aggregate => unreachable,
            .value_unit, .value_union, .value_slice => unreachable,
        }
    }
    try writer.writeAll("...");
}

/// `Box[i64]`, or `Pair[K, V].swap[T]` for a member.
pub fn writeInstance(
    comp: *const Compilation,
    writer: *Writer,
    index: Pool.Instance,
) Writer.Error!void {
    const instance = comp.instanceAt(index);
    const decl = comp.declAt(instance.decl);
    const args = comp.instanceArgs(index);

    var skip: usize = 0;
    if (decl.owner.unwrap()) |owner_index| {
        const owner = comp.declAt(owner_index);
        try writer.writeAll(comp.pool.stringText(owner.name));
        // the owner's parameters lead the argument list
        const owner_params = comp.typeParamCount(owner_index);
        skip = @min(owner_params, args.len);
        try writeArgs(comp, writer, args[0..skip]);
        try writer.writeByte('.');
    }
    try writer.writeAll(comp.pool.stringText(decl.name));
    try writeArgs(comp, writer, args[skip..]);
}

pub fn writeArgs(
    comp: *const Compilation,
    writer: *Writer,
    args: []const Pool.Index,
) Writer.Error!void {
    if (args.len == 0) return;
    try writer.writeByte('[');
    for (args, 0..) |arg, position| {
        if (position > 0) try writer.writeAll(", ");
        if (comp.pool.isType(arg)) {
            try writeType(comp, writer, arg);
        } else {
            try writeConstant(comp, writer, arg);
        }
    }
    try writer.writeByte(']');
}

/// `(a: i64, b: bool) i64`, for the IR header.
pub fn writeSignature(
    comp: *const Compilation,
    writer: *Writer,
    index: Pool.Instance,
) Writer.Error!void {
    const instance = comp.instanceAt(index);
    assert(instance.rows_state == .done or instance.rows_state == .poisoned);

    try writer.writeByte('(');
    for (comp.instanceRows(index), 0..) |row, position| {
        if (position > 0) try writer.writeAll(", ");
        try writer.print("{s}: ", .{comp.pool.stringText(row.name)});
        try writeType(comp, writer, row.type);
    }
    try writer.writeByte(')');
    if (instance.type != .void_type) {
        try writer.writeByte(' ');
        try writeType(comp, writer, instance.type);
    }
}

const aggregate_shown_max = 8;

pub fn writeConstant(
    comp: *const Compilation,
    writer: *Writer,
    value: Pool.Index,
) Writer.Error!void {
    switch (comp.pool.keyOf(value)) {
        .type_simple => |simple| {
            assert(simple == .poison);
            try writer.writeAll("<broken>");
        },
        .value_int => |it| {
            try writer.print("{d}", .{it.value});
            if (it.type != .untyped_int_type) {
                try writer.writeByte(':');
                try writeType(comp, writer, it.type);
            }
        },
        .value_float => |it| {
            try writer.print("{d}", .{it.value});
            if (it.type != .untyped_float_type) {
                try writer.writeByte(':');
                try writeType(comp, writer, it.type);
            }
        },
        // spelled the way it was written, so a struct names its fields
        .value_aggregate => |it| {
            const fields: ?[]const Compilation.Row = switch (comp.pool.keyOf(it.type)) {
                .type_struct => |instance| comp.instanceRows(instance),
                else => null,
            };
            if (fields != null) {
                try writeType(comp, writer, it.type);
                try writer.writeAll(".{ ");
            } else {
                try writer.writeByte('[');
            }

            for (it.elems, 0..) |element, position| {
                // a long constant would flood the line it sits on
                if (position == aggregate_shown_max) {
                    try writer.print(", +{d} more", .{it.elems.len - position});
                    break;
                }
                if (position > 0) try writer.writeAll(", ");
                if (fields) |rows| {
                    if (position < rows.len) {
                        try writer.print("{s}: ", .{comp.pool.stringText(rows[position].name)});
                    }
                }
                try writeConstant(comp, writer, element);
            }

            if (fields != null) try writer.writeAll(" }") else try writer.writeByte(']');
        },
        // a unit value is spelled as its name
        .value_unit => |unit_type| try writeType(comp, writer, unit_type),
        // the member the union holds, which the context types
        .value_union => |it| try writeConstant(comp, writer, it.value),
        // the bytes, then the view, so storage and a view of it never print alike
        .value_slice => |it| {
            try writeConstant(comp, writer, it.data);
            try writer.writeByte(':');
            try writeType(comp, writer, it.type);
        },
        .type_pointer, .type_array, .type_slice => unreachable,
        .type_struct, .type_unit, .type_union => unreachable,
    }
}

pub fn writeConstantBare(
    comp: *const Compilation,
    writer: *Writer,
    value: Pool.Index,
) Writer.Error!void {
    switch (comp.pool.keyOf(value)) {
        .value_int => |it| try writer.print("{d}", .{it.value}),
        .value_float => |it| try writer.print("{d}", .{it.value}),
        else => try writeConstant(comp, writer, value),
    }
}

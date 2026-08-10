//! The operations the compiler performs itself, reached as `@name`.

const std = @import("std");
const assert = std.debug.assert;

/// Spelled in source exactly as the tag is written, after the `@`.
pub const Builtin = enum {
    /// `@ptr_cast[T](pointer)`, retyping a pointer without moving it.
    ptr_cast,
    /// `@size_of[T]()`, the bytes a value of `T` occupies, a constant.
    size_of,
    /// `@align_of[T]()`, the alignment a value of `T` requires, a constant.
    align_of,
    /// `@min_int[T]()`, the lowest value the integer type `T` holds, a constant.
    min_int,
    /// `@max_int[T]()`, the highest value the integer type `T` holds, a constant.
    max_int,
    /// `@trap()`, stopping the program where it stands.
    trap,

    /// Validated before typing a call. Type rules live with the case that needs them.
    pub const Shape = struct {
        type_params: u8,
        params: u8,
    };

    pub fn shape(builtin: Builtin) Shape {
        return switch (builtin) {
            .ptr_cast => .{ .type_params = 1, .params = 1 },
            .size_of, .align_of, .min_int, .max_int => .{ .type_params = 1, .params = 0 },
            .trap => .{ .type_params = 0, .params = 0 },
        };
    }

    /// Whether only the standard library may reach it, which is what a builtin
    /// able to break a guarantee the checker made earns.
    pub fn stdOnly(builtin: Builtin) bool {
        return switch (builtin) {
            .ptr_cast => true,
            .size_of, .align_of, .min_int, .max_int, .trap => false,
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

    /// Sized from the table, so no call site has to check its buffers.
    pub const type_params_max = 1;
    pub const params_max = 1;
};

comptime {
    assert(@typeInfo(Builtin).@"enum".fields.len > 0);
    for (std.enums.values(Builtin)) |builtin| {
        assert(builtin.shape().type_params <= Builtin.type_params_max);
        assert(builtin.shape().params <= Builtin.params_max);
    }
}

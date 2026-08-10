//! The operations the compiler performs itself, reached as `intrinsic.name`.

const std = @import("std");
const assert = std.debug.assert;

/// Spelled in source exactly as the tag is written.
pub const Intrinsic = enum {
    /// `intrinsic.ptr_cast[T](pointer)`, retyping a pointer without moving it.
    ptr_cast,
    /// `intrinsic.size_of[T]()`, the bytes a value of `T` occupies, a constant.
    size_of,
    /// `intrinsic.align_of[T]()`, the alignment a value of `T` requires, a constant.
    align_of,
    /// `intrinsic.trap()`, stopping the program where it stands.
    trap,

    /// Validated before typing a call. Type rules live with the case that needs them.
    pub const Shape = struct {
        type_params: u8,
        params: u8,
    };

    pub fn shape(intrinsic: Intrinsic) Shape {
        return switch (intrinsic) {
            .ptr_cast => .{ .type_params = 1, .params = 1 },
            .size_of, .align_of => .{ .type_params = 1, .params = 0 },
            .trap => .{ .type_params = 0, .params = 0 },
        };
    }

    pub fn fromName(text: []const u8) ?Intrinsic {
        assert(text.len > 0);
        return std.meta.stringToEnum(Intrinsic, text);
    }

    /// For a suggestion when a name is missed.
    pub const names = std.meta.fieldNames(Intrinsic);
};

/// Sized from the table, so no call site has to check its buffers.
pub const type_params_max = 1;
pub const params_max = 1;

comptime {
    assert(@typeInfo(Intrinsic).@"enum".fields.len > 0);
    for (std.enums.values(Intrinsic)) |intrinsic| {
        assert(intrinsic.shape().type_params <= type_params_max);
        assert(intrinsic.shape().params <= params_max);
    }
}

//! A `u32` row number with a type of its own, so two tables never mix.

const std = @import("std");
const assert = std.debug.assert;

/// One per table. `name` is what tells two instantiations apart.
pub fn Index(comptime name: []const u8) type {
    comptime assert(name.len > 0);
    return enum(u32) {
        _,

        const Self = @This();

        pub const table = name;
        pub const Optional = OptionalOf(Self);

        pub fn from(raw: usize) Self {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(@as(u32, @intCast(raw)));
        }

        pub fn int(index: Self) u32 {
            return @intFromEnum(index);
        }

        pub fn toOptional(index: Self) Optional {
            const optional: Optional = @enumFromInt(@intFromEnum(index));
            assert(optional != .none);
            return optional;
        }
    };
}

/// Four bytes, unlike `?Index`, and still forces an `unwrap()`.
pub fn OptionalOf(comptime Handle: type) type {
    return enum(u32) {
        none = std.math.maxInt(u32),
        _,

        pub fn unwrap(optional: @This()) ?Handle {
            if (optional == .none) return null;
            return @enumFromInt(@intFromEnum(optional));
        }
    };
}

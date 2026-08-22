const std = @import("std");
const assert = std.debug.assert;

/// `name` does nothing but keep each instantiation a distinct type.
pub fn Index(comptime name: []const u8) type {
    comptime assert(name.len > 0);
    return enum(u32) {
        _,

        const Self = @This();

        pub const Optional = OptionalOf(Self);

        pub fn from(raw: usize) Self {
            assert(raw < std.math.maxInt(u32));
            return @enumFromInt(raw);
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

/// Four bytes where `?Index` would be eight, and you still have to unwrap.
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

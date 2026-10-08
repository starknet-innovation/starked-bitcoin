const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const stwo_core = b.dependency("stwo_core", .{
        .target = target,
        .optimize = optimize,
    }).module("stwo_core");

    const stwo_prover_engine = b.dependency("stwo_prover_engine", .{
        .target = target,
        .optimize = optimize,
    }).module("stwo_prover_engine");
    const stwo_cpu_backend = b.dependency("stwo_cpu_backend", .{
        .target = target,
        .optimize = optimize,
    }).module("stwo_cpu_backend");

    const lib = b.addModule("starked_bitcoin", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "stwo_core", .module = stwo_core },
            .{ .name = "stwo_prover_engine", .module = stwo_prover_engine },
            .{ .name = "stwo_cpu_backend", .module = stwo_cpu_backend },
            .{ .name = "stwo_proof_wire", .module = b.dependency("stwo_proof_wire", .{ .target = target, .optimize = optimize }).module("stwo_proof_wire") },
            .{ .name = "stwo_circuit_frontend", .module = b.dependency("stwo_circuit_frontend", .{ .target = target, .optimize = optimize }).module("stwo_circuit_frontend") },
            .{ .name = "stwo_circuit_cpu_integration", .module = b.dependency("stwo_circuit_cpu_integration", .{ .target = target, .optimize = optimize }).module("stwo_circuit_cpu_integration") },
        },
    });

    // AIRs exported from the Lean definitions (lean/), consumed verbatim.
    lib.addAnonymousImport("air:add32_chain", .{ .root_source_file = b.path("airs/add32_chain.json") });
    lib.addAnonymousImport("air:sha256_compress", .{ .root_source_file = b.path("airs/sha256_compress.json") });
    lib.addAnonymousImport("air:header_chain", .{ .root_source_file = b.path("airs/header_chain.json") });
    lib.addAnonymousImport("testdata:mainnet_headers_0_16", .{ .root_source_file = b.path("testdata/mainnet_headers_0_16.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_0_1024", .{ .root_source_file = b.path("testdata/mainnet_headers_0_1024.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_1984_2048", .{ .root_source_file = b.path("testdata/mainnet_headers_1984_2048.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_32192_32320", .{ .root_source_file = b.path("testdata/mainnet_headers_32192_32320.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_1973_1984", .{ .root_source_file = b.path("testdata/mainnet_headers_1973_1984.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_32181_32192", .{ .root_source_file = b.path("testdata/mainnet_headers_32181_32192.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_399989_400000", .{ .root_source_file = b.path("testdata/mainnet_headers_399989_400000.hex") });
    lib.addAnonymousImport("testdata:mainnet_headers_400000_400064", .{ .root_source_file = b.path("testdata/mainnet_headers_400000_400064.hex") });
    lib.addAnonymousImport("testdata:mainnet_header_399168", .{ .root_source_file = b.path("testdata/mainnet_header_399168.hex") });
    lib.addAnonymousImport("testdata:mainnet_header_30240", .{ .root_source_file = b.path("testdata/mainnet_header_30240.hex") });
    lib.addAnonymousImport("testdata:mainnet_hash_15", .{ .root_source_file = b.path("testdata/mainnet_hash_15.txt") });
    lib.addAnonymousImport("circuit:air_programs", .{ .root_source_file = b.path("third_party/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") });
    lib.addAnonymousImport("circuit:compiled_constraints", .{ .root_source_file = b.path("third_party/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") });
    lib.addAnonymousImport("air:probe_oracle", .{ .root_source_file = b.path("airs/probe_oracle.json") });
    lib.addAnonymousImport("air:byte_table", .{ .root_source_file = b.path("airs/byte_table.json") });
    lib.addAnonymousImport("air:byte_user", .{ .root_source_file = b.path("airs/byte_user.json") });

    // `zig build test -Dtest-filter=<substring>` runs only matching tests (the full suite takes ~16 min).
    const test_filters = b.option([]const []const u8, "test-filter", "Only run tests whose names contain this") orelse &.{};
    const tests = b.addTest(.{ .root_module = lib, .filters = test_filters });

    if (target.result.os.tag == .macos) {
        const dep_opts = .{ .target = target, .optimize = optimize };
        const spike = b.addExecutable(.{
            .name = "spike",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/bin/spike.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "starked_bitcoin", .module = lib },
                    .{ .name = "stwo_core", .module = stwo_core },
                    .{ .name = "stwo_cpu_backend", .module = stwo_cpu_backend },
                    .{ .name = "stwo_metal_backend", .module = b.dependency("stwo_metal_backend", dep_opts).module("stwo_metal_backend") },
                    .{ .name = "stwo_proof_wire", .module = b.dependency("stwo_proof_wire", dep_opts).module("stwo_proof_wire") },
                },
            }),
        });
        spike.linkLibC();
        spike.linkFramework("Foundation");
        spike.linkFramework("Metal");
        spike.linkSystemLibrary("objc");
        b.installArtifact(spike);
    }
    const test_step = b.step("test", "Run starked-bitcoin tests");
    test_step.dependOn(&b.addRunArtifact(tests).step);
}

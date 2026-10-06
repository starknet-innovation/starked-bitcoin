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
        },
    });

    // AIRs exported from the Lean definitions (lean/), consumed verbatim.
    lib.addAnonymousImport("air:add32_chain", .{ .root_source_file = b.path("airs/add32_chain.json") });
    lib.addAnonymousImport("air:sha256_compress", .{ .root_source_file = b.path("airs/sha256_compress.json") });
    lib.addAnonymousImport("air:probe_oracle", .{ .root_source_file = b.path("airs/probe_oracle.json") });

    const tests = b.addTest(.{ .root_module = lib });

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

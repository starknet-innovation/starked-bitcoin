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

    // The circuit CPU integration and its own instance of the recursion wire module (one module
    // per file per compilation, so its types match the integration's).
    const stwo_circuit_cpu = b.dependency("stwo_circuit_cpu_integration", .{ .target = target, .optimize = optimize }).module("stwo_circuit_cpu_integration");
    const stwo_wire = stwo_circuit_cpu.import_table.get("stwo_circuit_recursion_wire") orelse @panic("circuit CPU integration is missing its recursion wire module");

    // stwo's postcard proof encoding (block proof files), built from the submodule's source.
    const stwo_proof_wire = b.dependency("stwo_proof_wire", .{ .target = target, .optimize = optimize }).module("stwo_proof_wire");
    const stwo_postcard = b.createModule(.{
        .root_source_file = b.path("third_party/stwo-zig/src/interop/postcard.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "stwo_core", .module = stwo_core },
            .{ .name = "stwo_proof_wire", .module = stwo_proof_wire },
        },
    });

    const lib = b.addModule("starked_bitcoin", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "stwo_core", .module = stwo_core },
            .{ .name = "stwo_prover_engine", .module = stwo_prover_engine },
            .{ .name = "stwo_cpu_backend", .module = stwo_cpu_backend },
            .{ .name = "stwo_proof_wire", .module = stwo_proof_wire },
            .{ .name = "stwo_postcard", .module = stwo_postcard },
            .{ .name = "stwo_circuit_frontend", .module = b.dependency("stwo_circuit_frontend", .{ .target = target, .optimize = optimize }).module("stwo_circuit_frontend") },
            .{ .name = "stwo_circuit_cpu_integration", .module = stwo_circuit_cpu },
            .{ .name = "stwo_circuit_recursion_wire", .module = stwo_wire },
            // The Cairo frontend's STWZEVA programs, bundles and captured-AIR runtime (src/air/stwzeva.zig).
            .{ .name = "stwo_cairo_frontend", .module = stwo_circuit_cpu.import_table.get("stwo_cairo_frontend") orelse @panic("circuit CPU integration is missing the Cairo frontend") },
        },
    });

    // Native CPU composition kernels for our STWZEVA bundle (src/air/stwzeva.zig, `aot_airs`): stwo-zig's
    // C code generator (`src/tools/cairo_composition_cpu_codegen/bundle_main.zig`) run on the committed
    // bundle, wired as `integrations/circuit_cpu/composition_aot_build.zig` does for the circuit AIR.
    {
        const cairo_frontend = stwo_circuit_cpu.import_table.get("stwo_cairo_frontend").?;
        const bundle_path = "testdata/stwzeva/pubfree.bin";
        const bundle = b.build_root.handle.readFileAlloc(b.allocator, bundle_path, 64 << 20) catch @panic("missing " ++ bundle_path);
        var digest: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(bundle, &digest, .{});
        const program_count: usize = 7;
        const generator = b.addExecutable(.{
            .name = "stwzeva-cpu-codegen",
            .root_module = b.createModule(.{
                .root_source_file = b.path("third_party/stwo-zig/src/tools/cairo_composition_cpu_codegen/bundle_main.zig"),
                .target = b.graph.host,
                .optimize = .ReleaseFast,
            }),
        });
        const surface = b.createModule(.{
            .root_source_file = b.path("third_party/stwo-zig/src/frontends/cairo/codegen_surface.zig"),
            .target = b.graph.host,
            .optimize = .ReleaseFast,
        });
        surface.addImport("stwo_core", b.dependency("stwo_core", .{ .target = b.graph.host, .optimize = .ReleaseFast }).module("stwo_core"));
        generator.root_module.addImport("stwo_cairo", surface);
        const generate = b.addRunArtifact(generator);
        generate.addFileArg(b.path(bundle_path));
        generate.addArgs(&.{ b.fmt("{s}", .{std.fmt.bytesToHex(digest, .lower)}), "stwzeva_cpu_air", b.fmt("{d}", .{program_count}) });
        const directory = generate.addOutputDirectoryArg("stwzeva-cpu-aot");
        const registry = b.createModule(.{ .root_source_file = directory.path(b, "registry.zig"), .target = target, .optimize = optimize });
        registry.addImport("stwo_cairo_frontend", cairo_frontend);
        const kernels = b.addLibrary(.{
            .name = "stwzeva-cpu-kernels",
            .linkage = .static,
            .root_module = b.createModule(.{ .target = target, .optimize = optimize, .pic = true, .link_libc = true }),
        });
        for (0..program_count) |index| kernels.root_module.addCSourceFile(.{
            .file = directory.path(b, b.fmt("stwzeva_cpu_air_{d}.c", .{index})),
            .flags = &.{ "-std=c11", "-O3", "-fstrict-aliasing", "-fno-vectorize", "-fno-slp-vectorize", "-gline-tables-only" },
        });
        registry.linkLibrary(kernels);
        lib.addImport("stwzeva_cpu_aot", registry);
    }

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
    lib.addAnonymousImport("testdata:mmr_sides", .{ .root_source_file = b.path("testdata/mmr_sides.txt") });
    lib.addAnonymousImport("testdata:mainnet_hash_15", .{ .root_source_file = b.path("testdata/mainnet_hash_15.txt") });
    lib.addAnonymousImport("circuit:air_programs", .{ .root_source_file = b.path("third_party/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") });
    lib.addAnonymousImport("circuit:compiled_constraints", .{ .root_source_file = b.path("third_party/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") });
    lib.addAnonymousImport("air:probe_oracle", .{ .root_source_file = b.path("airs/probe_oracle.json") });
    lib.addAnonymousImport("air:byte_table", .{ .root_source_file = b.path("airs/byte_table.json") });
    lib.addAnonymousImport("air:byte_user", .{ .root_source_file = b.path("airs/byte_user.json") });
    lib.addAnonymousImport("air:blake2s_compress", .{ .root_source_file = b.path("airs/blake2s_compress.json") });
    lib.addAnonymousImport("air:blake2s_tree", .{ .root_source_file = b.path("airs/blake2s_tree.json") });
    lib.addAnonymousImport("air:header_chain_v7", .{ .root_source_file = b.path("airs/header_chain_v7.json") });
    lib.addAnonymousImport("air:node_glue", .{ .root_source_file = b.path("airs/node_glue.json") });
    lib.addAnonymousImport("air:genesis_checks", .{ .root_source_file = b.path("airs/genesis_checks.json") });
    lib.addAnonymousImport("air:leaf_glue", .{ .root_source_file = b.path("airs/leaf_glue.json") });
    lib.addAnonymousImport("air:block_bytes", .{ .root_source_file = b.path("airs/block_bytes.json") });
    lib.addAnonymousImport("air:block_reader", .{ .root_source_file = b.path("airs/block_reader.json") });
    lib.addAnonymousImport("air:block_sha", .{ .root_source_file = b.path("airs/block_sha.json") });
    lib.addAnonymousImport("air:block_msg", .{ .root_source_file = b.path("airs/block_msg.json") });
    lib.addAnonymousImport("air:block_fields", .{ .root_source_file = b.path("airs/block_fields.json") });
    lib.addAnonymousImport("air:block_merkle", .{ .root_source_file = b.path("airs/block_merkle.json") });
    lib.addAnonymousImport("air:block_tables", .{ .root_source_file = b.path("airs/block_tables.json") });
    lib.addAnonymousImport("air:block_walk", .{ .root_source_file = b.path("airs/block_walk.json") });
    lib.addAnonymousImport("air:block_ctx", .{ .root_source_file = b.path("airs/block_ctx.json") });
    lib.addAnonymousImport("air:block_anc", .{ .root_source_file = b.path("airs/block_anc.json") });
    lib.addAnonymousImport("air:block_wmerkle", .{ .root_source_file = b.path("airs/block_wmerkle.json") });
    lib.addAnonymousImport("air:block_undo", .{ .root_source_file = b.path("airs/block_undo.json") });
    lib.addAnonymousImport("air:block_b2msg", .{ .root_source_file = b.path("airs/block_b2msg.json") });
    lib.addAnonymousImport("air:block_b2s", .{ .root_source_file = b.path("airs/block_b2s.json") });
    lib.addAnonymousImport("air:extsum_test", .{ .root_source_file = b.path("airs/extsum_test.json") });
    lib.addAnonymousImport("air:composition_header_chain", .{ .root_source_file = b.path("airs/composition_header_chain.json") });
    lib.addAnonymousImport("air:composition_bytesys", .{ .root_source_file = b.path("airs/composition_bytesys.json") });
    lib.addAnonymousImport("air:composition_leaf", .{ .root_source_file = b.path("airs/composition_leaf.json") });
    lib.addAnonymousImport("air:balance_leaf", .{ .root_source_file = b.path("airs/balance_leaf.json") });
    lib.addAnonymousImport("air:statement_leaf", .{ .root_source_file = b.path("airs/statement_leaf.json") });
    lib.addAnonymousImport("air:leafhash_104", .{ .root_source_file = b.path("airs/leafhash_104.json") });
    lib.addAnonymousImport("air:leafhash_434", .{ .root_source_file = b.path("airs/leafhash_434.json") });
    lib.addAnonymousImport("air:leafhash_12", .{ .root_source_file = b.path("airs/leafhash_12.json") });
    lib.addAnonymousImport("air:leafhash_8", .{ .root_source_file = b.path("airs/leafhash_8.json") });
    lib.addAnonymousImport("air:channel_mix_u32s_1", .{ .root_source_file = b.path("airs/channel_mix_u32s_1.json") });
    lib.addAnonymousImport("air:channel_mix_u32s_8", .{ .root_source_file = b.path("airs/channel_mix_u32s_8.json") });
    lib.addAnonymousImport("air:channel_mix_u32s_10", .{ .root_source_file = b.path("airs/channel_mix_u32s_10.json") });
    lib.addAnonymousImport("air:channel_mix_qm31s_2", .{ .root_source_file = b.path("airs/channel_mix_qm31s_2.json") });
    lib.addAnonymousImport("air:channel_mix_qm31s_3757", .{ .root_source_file = b.path("airs/channel_mix_qm31s_3757.json") });
    lib.addAnonymousImport("air:channel_draw", .{ .root_source_file = b.path("airs/channel_draw.json") });
    lib.addAnonymousImport("air:channel_draw_qm31", .{ .root_source_file = b.path("airs/channel_draw_qm31.json") });
    lib.addAnonymousImport("air:channel_draw_point", .{ .root_source_file = b.path("airs/channel_draw_point.json") });
    lib.addAnonymousImport("air:channel_pow_mix", .{ .root_source_file = b.path("airs/channel_pow_mix.json") });
    lib.addAnonymousImport("air:channel_pow_check_0", .{ .root_source_file = b.path("airs/channel_pow_check_0.json") });
    lib.addAnonymousImport("air:channel_pow_check_4", .{ .root_source_file = b.path("airs/channel_pow_check_4.json") });
    lib.addAnonymousImport("air:channel_pow_check_26", .{ .root_source_file = b.path("airs/channel_pow_check_26.json") });
    lib.addAnonymousImport("air:transcript_lookups", .{ .root_source_file = b.path("airs/transcript_lookups.json") });
    lib.addAnonymousImport("air:transcript_plain", .{ .root_source_file = b.path("airs/transcript_plain.json") });
    lib.addAnonymousImport("air:merkle_node", .{ .root_source_file = b.path("airs/merkle_node.json") });
    lib.addAnonymousImport("air:deep_leaf", .{ .root_source_file = b.path("airs/deep_leaf.json") });
    lib.addAnonymousImport("air:block_leaf_ctx", .{ .root_source_file = b.path("airs/block_leaf_ctx.json") });
    lib.addAnonymousImport("air:block_node_glue", .{ .root_source_file = b.path("airs/block_node_glue.json") });
    lib.addAnonymousImport("air:block_leaf_sum", .{ .root_source_file = b.path("airs/block_leaf_sum.json") });
    lib.addAnonymousImport("air:seed_leaf", .{ .root_source_file = b.path("airs/seed_leaf.json") });
    lib.addAnonymousImport("air:block_leaf_checks", .{ .root_source_file = b.path("airs/block_leaf_checks.json") });
    lib.addAnonymousImport("air:oods_shift_leaf", .{ .root_source_file = b.path("airs/oods_shift_leaf.json") });
    lib.addAnonymousImport("vk:mainnet_test", .{ .root_source_file = b.path("vk/mainnet-q70-p26-l20.vk") });
    lib.addAnonymousImport("air:block_fpwalk", .{ .root_source_file = b.path("airs/block_fpwalk.json") });
    lib.addAnonymousImport("air:block_urec", .{ .root_source_file = b.path("airs/block_urec.json") });
    lib.addAnonymousImport("air:block_coin", .{ .root_source_file = b.path("airs/block_coin.json") });
    lib.addAnonymousImport("testdata:block_170", .{ .root_source_file = b.path("testdata/blocks/170.bin") });
    lib.addAnonymousImport("testdata:anc_170", .{ .root_source_file = b.path("testdata/anc/170.bin") });
    lib.addAnonymousImport("testdata:anc_481824", .{ .root_source_file = b.path("testdata/anc/481824.bin") });
    lib.addAnonymousImport("testdata:anc_709632", .{ .root_source_file = b.path("testdata/anc/709632.bin") });
    lib.addAnonymousImport("testdata:anc_970347", .{ .root_source_file = b.path("testdata/anc/970347.bin") });
    lib.addAnonymousImport("testdata:anc_774628", .{ .root_source_file = b.path("testdata/anc/774628.bin") });
    lib.addAnonymousImport("testdata:block_91722", .{ .root_source_file = b.path("testdata/blocks/91722.bin") });
    lib.addAnonymousImport("testdata:block_91812", .{ .root_source_file = b.path("testdata/blocks/91812.bin") });
    lib.addAnonymousImport("testdata:block_91842", .{ .root_source_file = b.path("testdata/blocks/91842.bin") });
    lib.addAnonymousImport("testdata:block_91880", .{ .root_source_file = b.path("testdata/blocks/91880.bin") });
    lib.addAnonymousImport("testdata:block_400000", .{ .root_source_file = b.path("testdata/blocks/400000.bin") });
    lib.addAnonymousImport("testdata:block_481824", .{ .root_source_file = b.path("testdata/blocks/481824.bin") });
    lib.addAnonymousImport("testdata:block_709632", .{ .root_source_file = b.path("testdata/blocks/709632.bin") });
    lib.addAnonymousImport("testdata:block_970347", .{ .root_source_file = b.path("testdata/blocks/970347.bin") });
    lib.addAnonymousImport("testdata:block_774628", .{ .root_source_file = b.path("testdata/blocks/774628.bin") });
    lib.addAnonymousImport("testdata:block_0", .{ .root_source_file = b.path("testdata/blocks/0.bin") });
    lib.addAnonymousImport("testdata:block_9", .{ .root_source_file = b.path("testdata/blocks/9.bin") });
    lib.addAnonymousImport("testdata:undo_0", .{ .root_source_file = b.path("testdata/undo/0.undo") });
    lib.addAnonymousImport("testdata:undo_170", .{ .root_source_file = b.path("testdata/undo/170.undo") });
    lib.addAnonymousImport("testdata:undo_91722", .{ .root_source_file = b.path("testdata/undo/91722.undo") });
    lib.addAnonymousImport("testdata:undo_91812", .{ .root_source_file = b.path("testdata/undo/91812.undo") });
    lib.addAnonymousImport("testdata:undo_91842", .{ .root_source_file = b.path("testdata/undo/91842.undo") });
    lib.addAnonymousImport("testdata:undo_91880", .{ .root_source_file = b.path("testdata/undo/91880.undo") });
    lib.addAnonymousImport("testdata:undo_400000", .{ .root_source_file = b.path("testdata/undo/400000.undo") });
    lib.addAnonymousImport("testdata:undo_481824", .{ .root_source_file = b.path("testdata/undo/481824.undo") });
    lib.addAnonymousImport("testdata:undo_709632", .{ .root_source_file = b.path("testdata/undo/709632.undo") });
    lib.addAnonymousImport("testdata:undo_970347", .{ .root_source_file = b.path("testdata/undo/970347.undo") });
    lib.addAnonymousImport("testdata:undo_774628", .{ .root_source_file = b.path("testdata/undo/774628.undo") });

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

        // GPU plan step 1: our lowered STWZEVA programs as Metal kernels (src/gpu/metal_parity.zig).
        const cairo_frontend = stwo_circuit_cpu.import_table.get("stwo_cairo_frontend").?;
        const metal_codegen = b.createModule(.{
            .root_source_file = b.path("third_party/stwo-zig/src/integrations/cairo_metal/eval_codegen.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "stwo_cairo_frontend", .module = cairo_frontend }},
        });
        const metal_parity = b.addTest(.{
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/gpu/metal_parity.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "starked_bitcoin", .module = lib },
                    .{ .name = "stwo_core", .module = stwo_core },
                    .{ .name = "stwo_prover_engine", .module = stwo_prover_engine },
                    .{ .name = "stwo_metal_backend", .module = b.dependency("stwo_metal_backend", dep_opts).module("stwo_metal_backend") },
                    .{ .name = "cairo_metal_eval_codegen", .module = metal_codegen },
                },
            }),
        });
        metal_parity.linkLibC();
        metal_parity.linkFramework("Foundation");
        metal_parity.linkFramework("Metal");
        metal_parity.linkSystemLibrary("objc");
        b.step("metal-parity", "STWZEVA programs of our AIRs as Metal kernels vs the interpreter").dependOn(&b.addRunArtifact(metal_parity).step);
    }
    // `chainproof`: the chain proof as a file (PROOF-STORE). Provenance: the commits it was built from.
    {
        const opts = b.addOptions();
        const repo = std.mem.trim(u8, b.run(&.{ "git", "-C", b.build_root.path orelse ".", "rev-parse", "HEAD" }), " \n");
        const dirty = std.mem.trim(u8, b.run(&.{ "git", "-C", b.build_root.path orelse ".", "status", "--porcelain", "--untracked-files=no" }), " \n").len != 0;
        opts.addOption([]const u8, "repo_commit", b.fmt("{s}{s}", .{ repo, if (dirty) "+dirty" else "" }));
        opts.addOption([]const u8, "stwo_commit", std.mem.trim(u8, b.run(&.{ "git", "-C", b.pathFromRoot("third_party/stwo-zig"), "rev-parse", "HEAD" }), " \n"));
        const chainproof = b.addExecutable(.{
            .name = "chainproof",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/bin/chainproof.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "starked_bitcoin", .module = lib },
                    .{ .name = "stwo_core", .module = stwo_core },
                    .{ .name = "build_options", .module = opts.createModule() },
                },
            }),
        });
        // The pinned production VK (70 queries, 26 PoW bits, segments up to 4096 headers).
        chainproof.root_module.addAnonymousImport("vk:mainnet", .{ .root_source_file = b.path("vk/mainnet-q70-p26-l20.vk") });
        chainproof.linkLibC();
        b.installArtifact(chainproof);
    }
    // `blockleaf`: BLOCK-REC measurement (a block proof verified in-circuit).
    {
        const bl = b.addExecutable(.{
            .name = "blockleaf",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/bin/blockleaf.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{.{ .name = "starked_bitcoin", .module = lib }},
            }),
        });
        bl.linkLibC();
        const run = b.addRunArtifact(bl);
        if (b.args) |args| run.addArgs(args);
        const demo = b.addExecutable(.{
            .name = "blockrec",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/bin/blockrec.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{.{ .name = "starked_bitcoin", .module = lib }},
            }),
        });
        demo.linkLibC();
        const drun = b.addRunArtifact(demo);
        if (b.args) |args| drun.addArgs(args);
        b.step("blockrec", "BLOCK-REC: two block leaves and a node from epoch proofs").dependOn(&drun.step);
        b.step("blockleaf", "BLOCK-REC: measure a block proof verified in-circuit").dependOn(&run.step);
    }
    // `oracle`: VL-ORACLE, the native verifier as oracle for the in-circuit verifier (FRI included).
    {
        const oracle = b.addExecutable(.{
            .name = "oracle",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/bin/oracle.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{.{ .name = "starked_bitcoin", .module = lib }},
            }),
        });
        oracle.linkLibC();
        b.step("oracle", "VL-ORACLE: native verifier vs circuit on mutated proofs").dependOn(&b.addRunArtifact(oracle).step);
    }
    const test_step = b.step("test", "Run starked-bitcoin tests");
    test_step.dependOn(&b.addRunArtifact(tests).step);
}

/* Host-only link stubs for the resident CUDA prover's checks (`zig build cuda-check -Dcuda=true`).
 * Never linked into a device build: there the real stwo-zig CUDA archive provides these symbols.
 * The checks type-check and link the device dispatch; they never execute it (every stub returns
 * an error status). Together with stwo-zig's `backends/cuda/runtime/stages/test_stubs.c` they
 * cover every native entry point the resident schedule calls. */
int stwo_exec_context_memcpy_h2d_async() { return 0; }
int stwo_accumulate_quotient_numerator_native_bucket_on() { return -1; }
int stwo_cairo_eval_materialize_params_on() { return -1; }
int stwo_circuit_degree_verdict_on() { return -1; }
int stwo_composition_lift_accumulate_on() { return -1; }
int stwo_constraint_expand_reversed_powers_on() { return -1; }
int stwo_cuda_device_snapshot() { return -1; }
int stwo_cuda_execution_provider() { return -1; }
int stwo_cuda_platform_snapshot() { return -1; }
int stwo_exec_context_alloc_u32() { return -1; }
int stwo_exec_context_create() { return -1; }
int stwo_exec_context_dependencies_reset() { return -1; }
int stwo_exec_context_destroy() { return -1; }
int stwo_exec_context_device() { return -1; }
int stwo_exec_context_free_u32() { return -1; }
int stwo_exec_context_identity() { return -1; }
int stwo_exec_context_join_all_lanes() { return -1; }
int stwo_exec_context_lane_count() { return -1; }
int stwo_exec_context_lane_stream() { return -1; }
int stwo_exec_context_memcpy_d2d_async() { return -1; }
int stwo_exec_context_memcpy_d2h_async() { return -1; }
int stwo_exec_context_memory_info() { return -1; }
int stwo_exec_context_memset_async() { return -1; }
int stwo_exec_context_nvtx_pop() { return -1; }
int stwo_exec_context_nvtx_push() { return -1; }
int stwo_exec_context_pool_current() { return -1; }
int stwo_exec_context_stream() { return -1; }
int stwo_exec_context_sync() { return -1; }
int stwo_exec_context_timing_begin() { return -1; }
int stwo_exec_context_timing_elapsed() { return -1; }
int stwo_exec_context_timing_mark() { return -1; }
int stwo_graph_capture_abort() { return -1; }
int stwo_graph_destroy() { return -1; }
int stwo_lde_n2b_addressed_on() { return -1; }
int stwo_native_aot_function_bind_with_globals() { return -1; }
int stwo_native_aot_function_destroy() { return -1; }
int stwo_native_aot_function_launch() { return -1; }
int stwo_native_aot_function_publish_pedersen() { return -1; }
int stwo_native_aot_loader_create() { return -1; }
int stwo_native_aot_loader_destroy() { return -1; }
int stwo_native_aot_loader_stats() { return -1; }
int stwo_static_cuda_module_build_identity() { return -1; }
int stwo_zig_cuda_aot_entry_count() { return -1; }
int stwo_witness_edge_gather_contiguous_on() { return -1; }

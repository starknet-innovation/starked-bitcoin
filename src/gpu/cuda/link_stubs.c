/* Host-only link stubs for the resident CUDA prover's checks (`zig build cuda-test -Dcuda=true`).
 * Never linked into a device build: there the real stwo-zig CUDA archive provides these symbols.
 * The checks type-check and link the device dispatch; they never execute it. */
int stwo_exec_context_memcpy_h2d_async() { return 0; }

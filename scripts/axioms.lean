-- The main theorems, whose axioms scripts/check.sh checks after `lake build` (run from lean/ with
-- `lake env lean ../scripts/axioms.lean`). The same list as docs/project/status.md § Verify the current state.
import StarkedAir
open StarkedAir.HeaderChain StarkedAir.Spec.Bitcoin
#print axioms header_chain_sound
#print axioms StarkedAir.Sha256.compress_sound_air
#print axioms pub_compose
#print axioms chain_from_genesis
#print axioms StarkedAir.HeaderTree.chain_from_genesis_T
#print axioms StarkedAir.Circuit.node_compose
#print axioms StarkedAir.Block.Fields.fields_sound_gen
#print axioms StarkedAir.Block.merkle_sound
#print axioms StarkedAir.Block.wmerkle_sound
#print axioms StarkedAir.Block.block_sound
#print axioms StarkedAir.Block.commit_sound
#print axioms StarkedAir.Block.hash_pub
#print axioms StarkedAir.SetPass.set_seg_sound
#print axioms StarkedAir.SetPass.set_seg_root
#print axioms StarkedAir.SetPass.set_root_sound
#print axioms StarkedAir.Circuit.ChainSeal.compressFinal_sound
#print axioms StarkedAir.Circuit.ChainSeal.checks_epoch
#print axioms StarkedAir.Circuit.ChainSeal.seal_digest
#print axioms StarkedAir.SetPass.set_root_soundW
#print axioms StarkedAir.Circuit.ChainSeal.seal_soundW
#print axioms StarkedAir.Circuit.ChainSeal.pathOps_sound
#print axioms StarkedAir.Circuit.ChainSeal.sealT_cpath
#print axioms StarkedAir.Circuit.ChainSeal.sealT_soundW
#print axioms StarkedAir.HeaderTree.planTree_fill
#print axioms StarkedAir.Circuit.RecCR.htree_soundWS

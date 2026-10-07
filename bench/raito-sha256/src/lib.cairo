//! SHA256d of `n` 80-byte headers (the genesis header with nonce = i), using Raito's Cairo
//! SHA-256. Each header costs 3 compressions, like the header-chain AIR.
use utils::sha256::compute_sha256_u32_array;

#[executable]
fn main(n: u32) -> u32 {
    let mut acc: u32 = 0;
    let mut i: u32 = 0;
    while i != n {
        let header = array![
            0x01000000, 0, 0, 0, 0, 0, 0, 0, 0, 0x3ba3edfd, 0x7a7b12b2, 0x7ac72c3e, 0x67768f61,
            0x7fc81bc3, 0x888a5132, 0x3a9fb8aa, 0x4b1e5e4a, 0x29ab5f49, 0xffff001d, i,
        ];
        let [a0, a1, a2, a3, a4, a5, a6, a7] = compute_sha256_u32_array(header, 0, 0);
        let [d0, _, _, _, _, _, _, _] = compute_sha256_u32_array(
            array![a0, a1, a2, a3, a4, a5, a6, a7], 0, 0,
        );
        acc = acc ^ d0;
        i += 1;
    }
    acc
}

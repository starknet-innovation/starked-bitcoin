// Differential fuzzing of the Lean header spec against Bitcoin Core's own code (proof review
// 2026-10-09, §5 item 9). This harness links Core's `pow.cpp`, `chain.cpp` and `arith_uint256.cpp`
// and prints random cases with Core's answers, one per line: `<case>\t<answer>`. `SpecCases.lean`
// answers the same cases from the Lean spec; `run.sh` compares them.
//
// Cases (big numbers as 64 hex digits, others decimal):
//   compact <nBits>                 SetCompact: "none" if negative, overflow or zero, else the target
//   getcompact <target hex>         GetCompact
//   next <nBits> <prevTime> <pst>   CalculateNextWorkRequired (mainnet; times as uint32 nTime), with
//                                   the previous nBits in the mainnet domain (its target <= powLimit)
//   nextany <nBits> <prevTime> <pst> the same with any nBits (informational: Core's 256-bit product
//                                   can wrap there, the spec's cannot)
//   proof <nBits>                   GetBlockProof
//   pow <hash hex> <nBits>          CheckProofOfWorkImpl (mainnet powLimit); hash bytes data()[0..31]
//   mtp <t0,t1,...>                 GetMedianTimePast of the newest of blocks with these times,
//                                   newest first (Core reads at most 11)
//
// Usage: core_cases <seed> <cases per kind>

#include <arith_uint256.h>
#include <chain.h>
#include <consensus/params.h>
#include <pow.h>
#include <uint256.h>

#include <cstdint>
#include <cstdio>
#include <memory>
#include <random>
#include <string>
#include <vector>

static std::mt19937_64 rng;

static uint64_t rnd(uint64_t n) { return n == 0 ? 0 : rng() % n; }

static std::string hex64(const arith_uint256& x) { return x.GetHex(); }

static Consensus::Params mainnet()
{
    Consensus::Params p{};
    p.powLimit = uint256{"00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff"};
    p.nPowTargetSpacing = 10 * 60;
    p.nPowTargetTimespan = 14 * 24 * 60 * 60;
    p.fPowAllowMinDifficultyBlocks = false;
    p.fPowNoRetargeting = false;
    p.enforce_BIP94 = false;
    return p;
}

static uint32_t nbits()
{
    switch (rnd(6)) {
    case 0: return uint32_t(rng());
    case 1: { // any size, mantissa of random width, sign bit sometimes
        uint32_t size = rnd(40);
        uint32_t width = rnd(4) == 0 ? 8 : (rnd(2) ? 16 : 23);
        uint32_t mant = uint32_t(rng()) & ((1u << width) - 1);
        if (rnd(4) == 0) mant |= 0x800000;
        return (size << 24) | (mant & 0xffffff);
    }
    case 2: { // mainnet-like: normalized mantissa, sizes near powLimit's
        uint32_t size = 0x17 + rnd(8);
        uint32_t mant = 0x8000 + rnd(0x800000 - 0x8000);
        return (size << 24) | mant;
    }
    case 3: { // the overflow boundaries: sizes 32..35 with mantissas around 0xff / 0xffff
        uint32_t size = 32 + rnd(4);
        uint32_t edges[] = {0, 1, 0xff, 0x100, 0xffff, 0x10000, 0x7fffff};
        return (size << 24) | edges[rnd(7)];
    }
    case 4: { // small sizes 0..3 (mantissa shifted right)
        uint32_t size = rnd(4);
        return (size << 24) | uint32_t(rnd(0x1000000));
    }
    default: { // around powLimit 0x1d00ffff
        uint32_t c[] = {0x1d00ffff, 0x1d010000, 0x1d00fffe, 0x1c7fffff, 0x1d7fffff, 0x1e00ffff, 0x1d008000, 0x1d007fff};
        return c[rnd(8)];
    }
    }
}

static arith_uint256 target()
{
    unsigned bits = rnd(257);
    arith_uint256 t{0};
    for (int i = 0; i < 4; ++i) t = (t << 64) | arith_uint256(rng());
    if (bits < 256) t = bits == 0 ? arith_uint256{0} : (t >> (256 - bits));
    if (rnd(5) == 0) { // mantissa with the top bit set after normalization
        unsigned s = rnd(30);
        t = arith_uint256(0x800000 | rnd(0x800000)) << (8 * s);
    }
    return t;
}

static uint256 hashBytes(unsigned zeros)
{
    std::vector<unsigned char> b(32);
    for (auto& x : b) x = uint8_t(rng());
    for (unsigned i = 0; i < zeros && i < 32; ++i) b[31 - i] = 0; // little-endian: high bytes last
    return uint256{std::span<const unsigned char>(b)};
}

int main(int argc, char** argv)
{
    if (argc != 3) {
        std::fprintf(stderr, "usage: core_cases <seed> <cases per kind>\n");
        return 2;
    }
    rng.seed(std::stoull(argv[1]));
    const long n = std::stol(argv[2]);
    const auto params = mainnet();

    for (long i = 0; i < n; ++i) {
        uint32_t b = nbits();
        bool neg, ovf;
        arith_uint256 t;
        t.SetCompact(b, &neg, &ovf);
        std::printf("compact %u\t%s\n", b, (neg || ovf || t == 0) ? "none" : hex64(t).c_str());
    }
    for (long i = 0; i < n; ++i) {
        arith_uint256 t = target();
        std::printf("getcompact %s\t%u\n", hex64(t).c_str(), t.GetCompact());
    }
    for (long i = 0; i < n; ++i) {
        // Mainnet domain: the previous nBits passed CheckProofOfWork (target <= powLimit).
        uint32_t b;
        do { b = nbits(); } while (!DeriveTarget(b, params.powLimit));
        uint32_t prev = uint32_t(rng());
        int64_t spans[] = {302399, 302400, 302401, 1209600, 4838399, 4838400, 4838401, 0, -1};
        int64_t span = rnd(3) == 0 ? spans[rnd(9)] : int64_t(rnd(12000000)) - 2000000;
        int64_t pst64 = int64_t(prev) - span;
        if (pst64 < 0 || pst64 > 0xffffffffLL) pst64 = rnd(1ull << 32);
        uint32_t pst = uint32_t(pst64);
        CBlockIndex last;
        last.nBits = b;
        last.nTime = prev;
        last.nHeight = 2015;
        std::printf("next %u %u %u\t%u\n", b, prev, pst, CalculateNextWorkRequired(&last, pst, params));
    }
    for (long i = 0; i < n; ++i) { // outside the mainnet domain: any previous nBits (informational)
        uint32_t b = nbits();
        uint32_t prev = uint32_t(rng()), pst = uint32_t(rng());
        CBlockIndex last;
        last.nBits = b;
        last.nTime = prev;
        last.nHeight = 2015;
        std::printf("nextany %u %u %u\t%u\n", b, prev, pst, CalculateNextWorkRequired(&last, pst, params));
    }
    for (long i = 0; i < n; ++i) {
        uint32_t b = nbits();
        CBlockIndex idx;
        idx.nBits = b;
        std::printf("proof %u\t%s\n", b, hex64(GetBlockProof(idx)).c_str());
    }
    for (long i = 0; i < n; ++i) {
        uint32_t b = nbits();
        uint256 h = hashBytes(rnd(33));
        if (rnd(2) == 0) { // a hash at the target's boundary: target + {-2..2}
            if (auto t = DeriveTarget(b, params.powLimit)) {
                int64_t d = int64_t(rnd(5)) - 2;
                arith_uint256 v = *t;
                if (d < 0) v -= arith_uint256(uint64_t(-d)); else v += arith_uint256(uint64_t(d));
                h = ArithToUint256(v);
            }
        }
        std::printf("pow %s %u\t%d\n", HexStr(h).c_str(), b, CheckProofOfWorkImpl(h, b, params) ? 1 : 0);
    }
    for (long i = 0; i < n; ++i) {
        unsigned k = 1 + rnd(14);
        uint32_t base = uint32_t(rng());
        std::vector<uint32_t> times(k); // newest first
        for (auto& x : times) x = rnd(3) == 0 ? base : uint32_t(base + rnd(20) - 10);
        std::vector<std::unique_ptr<CBlockIndex>> chain;
        for (unsigned j = 0; j < k; ++j) { // oldest first
            auto idx = std::make_unique<CBlockIndex>();
            idx->nTime = times[k - 1 - j];
            idx->nHeight = j;
            idx->pprev = chain.empty() ? nullptr : chain.back().get();
            chain.push_back(std::move(idx));
        }
        std::string list;
        for (unsigned j = 0; j < k; ++j) list += (j ? "," : "") + std::to_string(times[j]);
        std::printf("mtp %s\t%lld\n", list.c_str(), (long long)chain.back()->GetMedianTimePast());
    }
    return 0;
}

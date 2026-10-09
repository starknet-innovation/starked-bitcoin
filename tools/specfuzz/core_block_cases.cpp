// Differential fuzzing of the Lean *block* spec (Spec/Block.lean) against Bitcoin Core's own code:
// CScript::GetSigOpCount(false), ComputeMerkleRoot (with the mutation flag), CheckTransaction, and
// txid/wtxid over Core's serialization. Prints `<case>\t<Core's answer>` lines like core_cases.cpp;
// `SpecCases.lean` answers them from the spec.
//
// Cases (bytes as hex):
//   sigops <script>                 CScript(script).GetSigOpCount(false)
//   merkle <h1,h2,...>              ComputeMerkleRoot(leaves, &mutated): "<root> <0|1>" (internal order)
//   checktx <tx>                    CheckTransaction on the transaction serialized with witness:
//                                   "ok" or Core's reject reason
//   txids <tx>                      "<txid> <wtxid>" (internal byte order)
//
// Usage: core_block_cases <seed> <cases per kind>

#include <consensus/merkle.h>
#include <consensus/tx_check.h>
#include <consensus/validation.h>
#include <crypto/hex_base.h>
#include <primitives/transaction.h>
#include <script/script.h>
#include <streams.h>
#include <uint256.h>

#include <cstdint>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

static std::mt19937_64 rng;
static uint64_t rnd(uint64_t n) { return n == 0 ? 0 : rng() % n; }

static std::vector<unsigned char> script()
{
    std::vector<unsigned char> s;
    const unsigned len = rnd(4) == 0 ? rnd(8) : rnd(64);
    while (s.size() < len) {
        switch (rnd(8)) {
        case 0: s.push_back(0xac + rnd(4)); break;          // CHECKSIG(VERIFY), CHECKMULTISIG(VERIFY)
        case 1: { unsigned n = 1 + rnd(6); s.push_back(n); for (unsigned i = 0; i < n; ++i) s.push_back(rnd(4) ? 0xac + rnd(4) : uint8_t(rng())); break; }
        case 2: { s.push_back(0x4c); unsigned n = rnd(4) ? rnd(6) : 0xff; s.push_back(n); for (unsigned i = 0; i < n && i < 8; ++i) s.push_back(0xac); break; }
        case 3: { s.push_back(0x4d); s.push_back(rnd(5)); if (rnd(3)) s.push_back(rnd(2)); break; }
        case 4: { s.push_back(0x4e); for (unsigned i = 0; i < rnd(5); ++i) s.push_back(rnd(3)); break; }
        case 5: s.push_back(0); break;
        default: s.push_back(uint8_t(rng())); break;
        }
    }
    return s;
}

static uint256 hash32(bool zero)
{
    std::vector<unsigned char> b(32, 0);
    if (!zero) for (auto& x : b) x = uint8_t(rng());
    return uint256{std::span<const unsigned char>(b)};
}

static CAmount amount()
{
    switch (rnd(8)) {
    case 0: return -CAmount(1 + rnd(1000));                     // negative
    case 1: return MAX_MONEY + CAmount(rnd(3));                  // at or above MAX_MONEY
    case 2: return MAX_MONEY / 2 + CAmount(rnd(2));              // two of these may exceed the total
    case 3: return CAmount(rng());                               // any int64
    default: return CAmount(rnd(5000000000ULL));
    }
}

static CMutableTransaction transaction()
{
    CMutableTransaction tx;
    tx.version = rnd(3) ? uint32_t(1 + rnd(2)) : uint32_t(rng());
    const unsigned nin = 1 + rnd(3);
    for (unsigned i = 0; i < nin; ++i) {
        CTxIn in;
        const bool null = rnd(4) == 0;
        in.prevout = COutPoint(Txid::FromUint256(hash32(null)), null ? 0xffffffff : (rnd(3) ? uint32_t(rnd(4)) : uint32_t(rng())));
        if (rnd(6) == 0) in.prevout.n = 0xffffffff;
        unsigned slen = rnd(4) == 0 ? rnd(110) : rnd(6);
        in.scriptSig = CScript();
        for (unsigned j = 0; j < slen; ++j) in.scriptSig.push_back(uint8_t(rng()));
        in.nSequence = rnd(2) ? 0xffffffff : uint32_t(rng());
        if (rnd(3) == 0) {
            unsigned items = rnd(3);
            for (unsigned j = 0; j < items; ++j) {
                std::vector<unsigned char> item(rnd(40));
                for (auto& x : item) x = uint8_t(rng());
                in.scriptWitness.stack.push_back(item);
            }
        }
        tx.vin.push_back(in);
    }
    if (nin >= 2 && rnd(4) == 0) tx.vin[1].prevout = tx.vin[0].prevout; // duplicate inputs
    const unsigned nout = rnd(6) == 0 ? 0 : 1 + rnd(3);
    for (unsigned i = 0; i < nout; ++i) {
        std::vector<unsigned char> s = script();
        tx.vout.emplace_back(amount(), CScript(s.begin(), s.end()));
    }
    tx.nLockTime = rnd(2) ? 0 : uint32_t(rng());
    return tx;
}

static std::string hex(std::span<const unsigned char> b) { return HexStr(b); }

int main(int argc, char** argv)
{
    if (argc != 3) {
        std::fprintf(stderr, "usage: core_block_cases <seed> <cases per kind>\n");
        return 2;
    }
    rng.seed(std::stoull(argv[1]));
    const long n = std::stol(argv[2]);

    for (long i = 0; i < n; ++i) {
        std::vector<unsigned char> s = script();
        CScript cs(s.begin(), s.end());
        std::printf("sigops %s\t%u\n", s.empty() ? "-" : hex(s).c_str(), cs.GetSigOpCount(false));
    }
    for (long i = 0; i < n; ++i) {
        unsigned k = 1 + rnd(9);
        std::vector<uint256> leaves;
        for (unsigned j = 0; j < k; ++j) leaves.push_back(hash32(false));
        if (k >= 2 && rnd(2)) leaves[k - 1] = leaves[k - 2];                 // duplicated last pair
        if (k >= 4 && rnd(3) == 0) leaves[1] = leaves[0];                     // equal first pair
        if (k >= 6 && rnd(3) == 0) { leaves[k - 2] = leaves[k - 4]; leaves[k - 1] = leaves[k - 3]; } // CVE-2012-2459 shape
        bool mutated = false;
        uint256 root = ComputeMerkleRoot(leaves, &mutated);
        std::string list;
        for (unsigned j = 0; j < k; ++j) list += (j ? "," : "") + hex(leaves[j]);
        std::printf("merkle %s\t%s %d\n", list.c_str(), hex(root).c_str(), mutated ? 1 : 0);
    }
    for (long i = 0; i < n; ++i) {
        CTransaction tx{transaction()};
        DataStream ss;
        ss << TX_WITH_WITNESS(tx);
        TxValidationState state;
        bool ok = CheckTransaction(tx, state);
        std::printf("checktx %s\t%s\n", hex(MakeUCharSpan(ss)).c_str(), ok ? "ok" : state.GetRejectReason().c_str());
    }
    for (long i = 0; i < n; ++i) {
        CTransaction tx{transaction()};
        DataStream ss;
        ss << TX_WITH_WITNESS(tx);
        std::printf("txids %s\t%s %s\n", hex(MakeUCharSpan(ss)).c_str(), hex(tx.GetHash().ToUint256()).c_str(), hex(tx.GetWitnessHash().ToUint256()).c_str());
    }
    return 0;
}

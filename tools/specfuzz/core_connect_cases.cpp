// Differential fuzzing of Spec/ConnectRules.lean against Bitcoin Core's own code: the accurate sigop
// count, GetTransactionSigOpCost (legacy, P2SH and witness parts, through a CCoinsViewCache), and the
// BIP68 sequence locks (CalculateSequenceLocks, EvaluateSequenceLocks over a CBlockIndex chain).
// Prints `<case>\t<Core's answer>` lines; `SpecCases.lean` answers them from the spec.
//
// Cases (bytes as hex, "-" for empty):
//   sigacc <script>                               CScript(script).GetSigOpCount(true)
//   sigcost <strict> <tx> <spk0,spk1,...>         GetTransactionSigOpCost(tx, view, flags); the view
//                                                 holds a coin with script spk_i for input i; flags are
//                                                 P2SH|WITNESS|TAPROOT (strict 1) or none (strict 0)
//   seqlock <enforce> <t0,...,tH> <tx> <c0,c1,..> the block at height H of a chain with these block
//                                                 times connects tx, input i spending a coin of
//                                                 height c_i: "<minHeight> <minTime> <0|1>"
//
// Usage: core_connect_cases <seed> <cases per kind>

#include <chain.h>
#include <coins.h>
#include <consensus/consensus.h>
#include <consensus/tx_verify.h>
#include <crypto/hex_base.h>
#include <primitives/transaction.h>
#include <script/interpreter.h>
#include <script/script.h>
#include <streams.h>
#include <uint256.h>

#include <cstdint>
#include <cstdio>
#include <memory>
#include <random>
#include <string>
#include <vector>

using Bytes = std::vector<unsigned char>;
static std::mt19937_64 rng;
static uint64_t rnd(uint64_t n) { return n == 0 ? 0 : rng() % n; }
static Bytes randBytes(unsigned n) { Bytes b(n); for (auto& x : b) x = uint8_t(rng()); return b; }
static void append(Bytes& a, const Bytes& b) { a.insert(a.end(), b.begin(), b.end()); }

// A script made of the pieces the accurate count distinguishes: CHECKSIG, CHECKMULTISIG after OP_n or
// after something else, pushes (which hide opcodes), truncated pushes, random bytes.
static Bytes sigScript()
{
    Bytes s;
    const unsigned len = rnd(4) == 0 ? rnd(6) : rnd(48);
    while (s.size() < len) {
        switch (rnd(10)) {
        case 0: s.push_back(0xac + rnd(2)); break;
        case 1: case 2: s.push_back(0x4f + rnd(19)); s.push_back(0xae + rnd(2)); break; // OP_1NEGATE..OP_NOP around OP_1..OP_16
        case 3: s.push_back(0xae + rnd(2)); break;
        case 4: { unsigned n = 1 + rnd(5); s.push_back(n); for (unsigned i = 0; i < n; ++i) s.push_back(rnd(3) ? 0x51 + rnd(16) : 0xae); break; }
        case 5: { s.push_back(0x4c); unsigned n = rnd(4) ? rnd(5) : 0xff; s.push_back(n); for (unsigned i = 0; i < n && i < 6; ++i) s.push_back(0xae); break; }
        case 6: s.push_back(0x51 + rnd(16)); break;
        case 7: { s.push_back(0x4d); s.push_back(rnd(4)); if (rnd(3)) s.push_back(rnd(2)); break; }
        case 8: s.push_back(0); break;
        default: s.push_back(uint8_t(rng())); break;
        }
    }
    return s;
}

// A witness program or something close to one.
static Bytes witnessLike()
{
    Bytes s;
    const unsigned v = rnd(6) == 0 ? rnd(256) : (rnd(2) ? 0 : 0x50 + rnd(18));
    unsigned n;
    switch (rnd(6)) { case 0: n = 20; break; case 1: case 2: n = 32; break; case 3: n = rnd(4); break; case 4: n = 38 + rnd(5); break; default: n = 2 + rnd(40); }
    s.push_back(v);
    s.push_back(rnd(8) == 0 ? n + rnd(3) - 1 : n);
    append(s, randBytes(n));
    return s;
}

static Bytes p2shLike()
{
    Bytes s{0xa9, 0x14};
    append(s, randBytes(20));
    s.push_back(0x87);
    switch (rnd(12)) { case 0: s[0] = 0xaa; break; case 1: s[1] = 0x15; break; case 2: s[22] = 0x88; break; case 3: s.push_back(0); break; case 4: s.pop_back(); break; default: break; }
    return s;
}

static Bytes spentScript()
{
    switch (rnd(8)) {
    case 0: case 1: case 2: return p2shLike();
    case 3: case 4: case 5: return witnessLike();
    case 6: return sigScript();
    default: { Bytes s{0x76, 0xa9, 0x14}; append(s, randBytes(20)); s.push_back(0x88); s.push_back(0xac); return s; }
    }
}

static void push(Bytes& s, const Bytes& d)
{
    const unsigned form = rnd(6);
    if (d.size() < 0x4c && form) s.push_back(d.size());
    else if (d.size() <= 0xff && form != 1) { s.push_back(0x4c); s.push_back(d.size()); }
    else if (form != 2) { s.push_back(0x4d); s.push_back(d.size() & 0xff); s.push_back(d.size() >> 8); }
    else { s.push_back(0x4e); s.push_back(d.size() & 0xff); s.push_back(d.size() >> 8); s.push_back(0); s.push_back(0); }
    append(s, d);
}

// A scriptSig: mostly pushes ending with a redeem script (a sigop script or a witness program),
// sometimes with a non-push opcode, a truncated push, or a last opcode that pushes nothing.
static Bytes scriptSig()
{
    Bytes s;
    if (rnd(10) == 0) return s;
    const unsigned items = rnd(3);
    for (unsigned i = 0; i < items; ++i) {
        if (rnd(8) == 0) s.push_back(rnd(2) ? 0x61 + rnd(80) : 0x4f + rnd(18));
        else push(s, randBytes(rnd(12)));
    }
    push(s, rnd(2) ? sigScript() : witnessLike());
    switch (rnd(12)) {
    case 0: s.push_back(0x51 + rnd(16)); break;                // ends with OP_n: the last item is empty
    case 1: s.push_back(0); break;
    case 2: s.push_back(0xac + rnd(4)); break;                 // not push-only
    case 3: s.push_back(1 + rnd(0x4b)); break;                 // truncated push
    case 4: if (!s.empty()) s.pop_back(); break;
    default: break;
    }
    return s;
}

static std::string hex(std::span<const unsigned char> b) { return b.empty() ? "-" : HexStr(b); }

// A lock: mostly small (so it can be met), sometimes with the mask's top bit, sometimes any 16 bits.
static uint32_t lockValue(unsigned small)
{
    switch (rnd(8)) { case 0: return 0x8000 | uint32_t(rnd(small)); case 1: return uint32_t(rnd(0x10000)); default: return uint32_t(rnd(small)); }
}

static CMutableTransaction transaction(bool allow_coinbase)
{
    CMutableTransaction tx;
    tx.version = rnd(4) ? uint32_t(rnd(4)) : uint32_t(rng());
    const bool coinbase = allow_coinbase && rnd(8) == 0;
    const unsigned nin = coinbase ? 1 : 1 + rnd(4);
    for (unsigned i = 0; i < nin; ++i) {
        CTxIn in;
        Bytes h = randBytes(32);
        in.prevout = coinbase ? COutPoint() : COutPoint(Txid::FromUint256(uint256{std::span<const unsigned char>(h)}), uint32_t(i));
        Bytes ss = scriptSig();
        in.scriptSig = CScript(ss.begin(), ss.end());
        switch (rnd(6)) {
        case 0: in.nSequence = 0xffffffff; break;
        case 1: in.nSequence = uint32_t(rng()); break;
        case 2: case 3: in.nSequence = lockValue(40) | (rnd(4) ? 0 : uint32_t(rng()) & 0x7fbf0000); break;             // height lock
        default: in.nSequence = (1u << 22) | lockValue(24) | (rnd(4) ? 0 : uint32_t(rng()) & 0x7fbf0000); break;        // time lock
        }
        if (rnd(8) == 0) in.nSequence |= 1u << 31;
        if (rnd(3)) {
            const unsigned items = rnd(3);
            for (unsigned j = 0; j < items; ++j) in.scriptWitness.stack.push_back(randBytes(rnd(34)));
            if (rnd(4)) in.scriptWitness.stack.push_back(sigScript());
        }
        tx.vin.push_back(in);
    }
    const unsigned nout = 1 + rnd(3);
    for (unsigned i = 0; i < nout; ++i) {
        Bytes s = rnd(2) ? sigScript() : spentScript();
        tx.vout.emplace_back(CAmount(rnd(5000000000ULL)), CScript(s.begin(), s.end()));
    }
    tx.nLockTime = 0;
    return tx;
}

int main(int argc, char** argv)
{
    if (argc != 3) {
        std::fprintf(stderr, "usage: core_connect_cases <seed> <cases per kind>\n");
        return 2;
    }
    rng.seed(std::stoull(argv[1]));
    const long n = std::stol(argv[2]);

    for (long i = 0; i < n; ++i) {
        Bytes s = sigScript();
        std::printf("sigacc %s\t%u\n", hex(s).c_str(), CScript(s.begin(), s.end()).GetSigOpCount(true));
    }
    for (long i = 0; i < n; ++i) {
        const CTransaction tx{transaction(true)};
        const bool strict = rnd(8) != 0;
        CCoinsViewCache view(&CoinsViewEmpty::Get());
        std::string list;
        for (size_t j = 0; j < tx.vin.size(); ++j) {
            Bytes spk = spentScript();
            while (CScript(spk.begin(), spk.end()).IsUnspendable()) spk = spentScript(); // AddCoin drops those
            if (!tx.IsCoinBase()) view.AddCoin(tx.vin[j].prevout, Coin(CTxOut(CAmount(1), CScript(spk.begin(), spk.end())), 1, false), false);
            list += (j ? "," : "") + hex(spk);
        }
        const script_verify_flags flags{strict ? script_verify_flags{SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_WITNESS | SCRIPT_VERIFY_TAPROOT} : script_verify_flags{SCRIPT_VERIFY_NONE}};
        DataStream ss;
        ss << TX_WITH_WITNESS(tx);
        std::printf("sigcost %d %s %s\t%lld\n", strict ? 1 : 0, hex(MakeUCharSpan(ss)).c_str(), list.c_str(), (long long)GetTransactionSigOpCost(tx, view, flags));
    }
    for (long i = 0; i < n; ++i) {
        const int height = 1 + int(rnd(4) == 0 ? rnd(12) : rnd(60));
        // Half the chains have a fixed step between block times (so median times past differ by
        // multiples of the 512 s unit) with an occasional second of jitter: locks met exactly or
        // missed by one second.
        const bool regular = rnd(2) == 0;
        static const uint32_t steps[] = {512, 256, 1024, 600};
        const uint32_t step = steps[rnd(4)];
        std::vector<std::unique_ptr<CBlockIndex>> chain;
        std::string times;
        uint32_t t = 1500000000 + uint32_t(rnd(1000000));
        for (int h = 0; h <= height; ++h) {
            auto bi = std::make_unique<CBlockIndex>();
            bi->nHeight = h;
            bi->pprev = h ? chain.back().get() : nullptr;
            if (regular) {
                t += step;
                bi->nTime = rnd(4) ? t : t + uint32_t(rnd(3)) - 1;
            } else {
                t += uint32_t(rnd(1200));
                bi->nTime = rnd(3) ? t : t - uint32_t(rnd(4000)) + uint32_t(rnd(4000));
            }
            bi->BuildSkip();
            times += (h ? "," : "") + std::to_string(bi->nTime);
            chain.push_back(std::move(bi));
        }
        CMutableTransaction mtx{transaction(false)};
        std::vector<int> prev;
        std::string list;
        for (size_t j = 0; j < mtx.vin.size(); ++j) {
            int c = rnd(5) == 0 ? int(rnd(3)) : int(rnd(height + 1));
            // Half the inputs sit at their lock's boundary: the coin's height is the block's minus the
            // lock (height locks; time locks on a regular chain with a 512 s step), give or take one.
            if (rnd(2)) {
                const int lock = int(mtx.vin[j].nSequence & 0xffff);
                const int at = height - lock + int(rnd(3)) - 1;
                if (lock < 64 && at >= 0 && at <= height) c = at;
            }
            prev.push_back(c);
            list += (j ? "," : "") + std::to_string(c);
        }
        const CTransaction tx{mtx};
        const bool enforce = rnd(8) != 0;
        const auto pair = CalculateSequenceLocks(tx, enforce ? LOCKTIME_VERIFY_SEQUENCE : 0, prev, *chain.back());
        const bool ok = EvaluateSequenceLocks(*chain.back(), pair);
        DataStream ss;
        ss << TX_WITH_WITNESS(tx);
        std::printf("seqlock %d %s %s %s\t%d %lld %d\n", enforce ? 1 : 0, times.c_str(), hex(MakeUCharSpan(ss)).c_str(), list.c_str(), pair.first, (long long)pair.second, ok ? 1 : 0);
    }
    return 0;
}

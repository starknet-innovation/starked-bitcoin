// Stubs for symbols that Core's coins.cpp and script/interpreter.cpp reference but that the functions
// under test (GetTransactionSigOpCost, CalculateSequenceLocks, EvaluateSequenceLocks) never call:
// signature verification, logging, the coins cache's hash salt. Each stub that must not run aborts.
#include <pubkey.h>
#include <random.h>
#include <util/check.h>
#include <util/log.h>
#include <util/moneystr.h>
#include <util/threadnames.h>
#include <util/time.h>

#include <cstdio>
#include <cstdlib>

[[noreturn]] static void never(const char* what) { std::fprintf(stderr, "stub called: %s\n", what); std::abort(); }

bool CPubKey::Verify(const uint256&, const std::vector<unsigned char>&) const { never("CPubKey::Verify"); }
bool CPubKey::CheckLowS(const std::vector<unsigned char>&) { never("CPubKey::CheckLowS"); }
bool XOnlyPubKey::VerifySchnorr(const uint256&, std::span<const unsigned char>) const { never("VerifySchnorr"); }
bool XOnlyPubKey::CheckTapTweak(const XOnlyPubKey&, const uint256&, bool) const { never("CheckTapTweak"); }
std::string FormatMoney(CAmount) { never("FormatMoney"); }
void assertion_fail(const std::source_location& loc, std::string_view a)
{
    std::fprintf(stderr, "%s:%u: assertion failed: %.*s\n", loc.file_name(), unsigned(loc.line()), int(a.size()), a.data());
    std::abort();
}
std::chrono::seconds GetMockTime() { return std::chrono::seconds{0}; }
std::string util::ThreadGetInternalName() { return "specfuzz"; }
void util::log::Log(util::log::Entry) {}
// The salt of the coins cache's hasher: any fixed key gives the same map contents.
static const std::array<std::byte, 32> ZERO_KEY{};
FastRandomContext::FastRandomContext(bool) noexcept : requires_seed(false), rng(ZERO_KEY) {}
void FastRandomContext::RandomSeed() noexcept { requires_seed = false; }

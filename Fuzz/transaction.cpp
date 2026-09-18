// Differential context-free transaction observations against libbitcoinkernel.
// See README.md for the response format, comparison domain, and proof boundary.
//
// Core reference (the exact revision is selected by ../fuzz.toml):
// https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.cpp#L513-L522
// https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/kernel/bitcoinkernel.cpp#L562-L575

#include <kernel/bitcoinkernel.h>
#include <lean/lean.h>
#include "transaction_cases.h"

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <memory>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

extern "C" {
void lean_initialize();
lean_obj_res initialize_btc_x2dverified_Fuzz_Transaction(uint8_t builtin);
// The argument is owned: this call consumes its Lean reference.
lean_obj_res btc_verified_transaction_observe(lean_obj_arg input);
}

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define BTC_VERIFIED_HAS_LSAN 1
#endif
#endif

#if defined(BTC_VERIFIED_HAS_LSAN)
extern "C" void __lsan_disable();
extern "C" void __lsan_enable();
#endif

namespace {

using Bytes = std::vector<uint8_t>;
using Input = std::span<const uint8_t>;
using LeanObject = std::unique_ptr<lean_object, decltype(&lean_dec)>;
using Transaction =
    std::unique_ptr<btck_Transaction, decltype(&btck_transaction_destroy)>;
using ValidationState =
    std::unique_ptr<btck_TxValidationState, decltype(&btck_tx_validation_state_destroy)>;

// The pinned Lean runtime and Lake objects are prebuilt without ASan. Module
// initialization retains GMP values and mutexes, and the small regression
// suite retains one more GMP value. Ignore allocations inside those Lean calls
// while leaving Core and this C++ harness subject to LeakSanitizer.
class LeanAllocationScope {
public:
    LeanAllocationScope() noexcept
    {
#if defined(BTC_VERIFIED_HAS_LSAN)
        __lsan_disable();
#endif
    }

    ~LeanAllocationScope()
    {
#if defined(BTC_VERIFIED_HAS_LSAN)
        __lsan_enable();
#endif
    }

    LeanAllocationScope(const LeanAllocationScope&) = delete;
    LeanAllocationScope& operator=(const LeanAllocationScope&) = delete;
};

constexpr std::string_view mismatch_injection_token{"transaction-observation-v1"};
std::atomic_size_t fuzz_executions{0};

bool deliberate_mismatch_enabled()
{
    const char* value = std::getenv("BTC_VERIFIED_INJECT_MISMATCH");
    return value != nullptr && value == mismatch_injection_token;
}

void print_hex(const char* label, Input bytes)
{
    std::fprintf(stderr, "%s (%zu bytes): ", label, bytes.size());
    for (const uint8_t byte : bytes.first(std::min(bytes.size(), size_t{256}))) {
        std::fprintf(stderr, "%02x", static_cast<unsigned int>(byte));
    }
    if (bytes.size() > 256) std::fputs(" ... (prefix only)", stderr);
    std::fputc('\n', stderr);
}

[[noreturn]] void fail(const char* reason, Input input, Input core = {}, Input lean = {})
{
    std::fprintf(stderr, "btc-verified transaction fuzz failure: %s\n", reason);
    std::fprintf(stderr, "btc-verified fuzz executions before failure: %zu\n",
                 fuzz_executions.load(std::memory_order_relaxed));
    if (const char* artifact = std::getenv("BTC_VERIFIED_FAILURE_ARTIFACT");
        artifact != nullptr && *artifact != '\0') {
        try {
            const std::filesystem::path path{artifact};
            if (!path.parent_path().empty()) {
                std::filesystem::create_directories(path.parent_path());
            }
            std::ofstream file(path, std::ios::binary);
            file.exceptions(std::ios::failbit | std::ios::badbit);
            if (!input.empty()) {
                file.write(reinterpret_cast<const char*>(input.data()), input.size());
            }
            std::fprintf(stderr, "saved complete failure input: %s\n", path.string().c_str());
        } catch (const std::exception& error) {
            std::fprintf(stderr, "could not save complete failure input: %s\n", error.what());
        }
    }
    // libFuzzer also saves the complete triggering input during a campaign.
    print_hex("input", input);
    print_hex("Core response", core);
    print_hex("Lean response", lean);
    std::fflush(stderr);
    std::abort();
}

void initialize_lean()
{
    // Mirror the executable initialization emitted by the pinned Lean compiler.
    // The module initializer also initializes its imported modules. Its ABI is
    // package-qualified and takes only `builtin` in Lean v4.30.0-rc2.
    static const bool initialized = [] {
        LeanAllocationScope lean_allocations;
        lean_initialize();
        LeanObject result{initialize_btc_x2dverified_Fuzz_Transaction(1), &lean_dec};
        lean_io_mark_end_initialization();
        if (lean_io_result_is_error(result.get())) {
            lean_io_result_show_error(result.get());
            fail("Lean module initialization failed", {});
        }
        lean_init_task_manager();
        if (std::atexit(lean_finalize_task_manager) != 0) {
            fail("could not register Lean runtime cleanup", {});
        }
        return true;
    }();
    (void)initialized;
}

int append_serialized_bytes(const void* data, size_t size, void* user_data) noexcept
{
    if (size == 0) return 0;
    auto& output = *static_cast<Bytes*>(user_data);
    const auto* bytes = static_cast<const uint8_t*>(data);
    try {
        output.insert(output.end(), bytes, bytes + size);
        return 0;
    } catch (...) {
        // Do not unwind a C++ exception through the C callback boundary. Core
        // reports a failed writer through transaction_to_bytes's return code.
        return 1;
    }
}

void append_word(Bytes& output, uint64_t value, size_t width)
{
    for (size_t i = 0; i < width; ++i) output.push_back((value >> (8 * i)) & 0xff);
}

void append_blob(Bytes& output, Input bytes)
{
    append_word(output, bytes.size(), 8);
    output.insert(output.end(), bytes.begin(), bytes.end());
}

template <typename Write>
void append_written_blob(Bytes& output, Write write)
{
    Bytes bytes;
    if (write(append_serialized_bytes, &bytes) != 0) {
        throw std::runtime_error("Core writer callback failed");
    }
    append_blob(output, bytes);
}

Bytes core_observe(Input input)
{
    const Transaction transaction{
        btck_transaction_create(input.data(), input.size()), &btck_transaction_destroy};
    if (!transaction) return {0};

    const ValidationState state{btck_tx_validation_state_create(), &btck_tx_validation_state_destroy};
    if (!state) throw std::runtime_error("Core validation-state allocation failed");
    const int checks = btck_transaction_check(transaction.get(), state.get());
    const auto mode = btck_tx_validation_state_get_validation_mode(state.get());
    const auto reason = btck_tx_validation_state_get_tx_validation_result(state.get());
    if ((checks != 0 && checks != 1) ||
        mode != (checks ? btck_ValidationMode_VALID : btck_ValidationMode_INVALID) ||
        reason != (checks ? btck_TxValidationResult_UNSET : btck_TxValidationResult_CONSENSUS)) {
        throw std::runtime_error("Unexpected Core CheckTransaction status contract");
    }
    Bytes result{1, static_cast<uint8_t>(checks)};
    append_written_blob(result, [&](auto writer, void* data) {
        return btck_transaction_to_bytes(transaction.get(), writer, data);
    });
    const size_t inputs = btck_transaction_count_inputs(transaction.get());
    const size_t outputs = btck_transaction_count_outputs(transaction.get());
    append_word(result, inputs, 8);
    append_word(result, outputs, 8);
    append_word(result, btck_transaction_get_locktime(transaction.get()), 4);
    for (size_t i = 0; i < inputs; ++i) {
        const auto* input_handle = btck_transaction_get_input_at(transaction.get(), i);
        const auto* outpoint = btck_transaction_input_get_out_point(input_handle);
        uint8_t hash[32];
        btck_txid_to_bytes(btck_transaction_out_point_get_txid(outpoint), hash);
        result.insert(result.end(), std::begin(hash), std::end(hash));
        append_word(result, btck_transaction_out_point_get_index(outpoint), 4);
        append_word(result, btck_transaction_input_get_sequence(input_handle), 4);
        append_written_blob(result, [&](auto writer, void* data) {
            return btck_transaction_input_get_script_sig(input_handle, writer, data);
        });
        const auto* witness = btck_transaction_input_get_witness_stack(input_handle);
        const size_t items = btck_witness_stack_count_items(witness);
        append_word(result, items, 8);
        for (size_t j = 0; j < items; ++j) {
            append_written_blob(result, [&](auto writer, void* data) {
                return btck_witness_stack_get_item_at(witness, j, writer, data);
            });
        }
    }
    for (size_t i = 0; i < outputs; ++i) {
        const auto* output = btck_transaction_get_output_at(transaction.get(), i);
        // Conversion to uint64_t is defined modulo 2^64: compare the signed
        // Core amount's bit pattern to the model's UInt64 wire representation.
        append_word(result, static_cast<uint64_t>(btck_transaction_output_get_amount(output)), 8);
        append_written_blob(result, [&](auto writer, void* data) {
            return btck_script_pubkey_to_bytes(btck_transaction_output_get_script_pubkey(output),
                                             writer, data);
        });
    }
    return result;
}

Bytes lean_observe(Input input)
{
    LeanObject bytes{lean_alloc_sarray(1, input.size(), input.size()), &lean_dec};
    if (!input.empty()) {
        std::memcpy(lean_sarray_cptr(bytes.get()), input.data(), input.size());
    }
    lean_object* observed;
    {
        LeanAllocationScope lean_allocations;
        observed = btc_verified_transaction_observe(bytes.release());
    }
    const LeanObject result{observed, &lean_dec};
    if (!result || lean_is_scalar(result.get()) || !lean_is_sarray(result.get()) ||
        lean_sarray_elem_size(result.get()) != 1) {
        throw std::runtime_error("Lean returned an invalid ByteArray representation");
    }
    const size_t size = lean_sarray_size(result.get());
    const uint8_t* data = lean_sarray_cptr(result.get());
    if (size == 0 || data[0] > 1 || (data[0] == 0 && size != 1) ||
        (data[0] == 1 && (size < 30 || data[1] > 1))) {
        throw std::runtime_error("Lean returned an invalid result tag");
    }
    return Bytes{data, data + size};
}

const char* mismatch_reason(Input core, Input lean)
{
    if (core[0] != lean[0]) return "prefix parse acceptance differs";
    if (core[0] == 0) return "malformed rejection response";
    if (core[1] != lean[1]) return "context-free transaction check differs";
    return "serialization or decoded field observation differs";
}

void compare_input(Input input, const transaction_cases::Case* expected = nullptr)
{
    try {
        const Bytes core = core_observe(input);
        Bytes lean = lean_observe(input);
        if (deliberate_mismatch_enabled()) {
            // Negative control for the surrounding CI runner. Mutate only the
            // already-validated observation, never either implementation.
            std::fputs("btc-verified: deliberate mismatch injection enabled\n", stderr);
            if (lean[0] == 1) lean[1] ^= 1;
            else lean[0] ^= 1;
        }
        if (core != lean) {
            if (expected) std::fprintf(stderr, "deterministic case: %s\n", expected->name.c_str());
            const auto difference = std::mismatch(core.begin(), core.end(), lean.begin(), lean.end());
            std::fprintf(stderr, "first differing response offset: %zu\n",
                         static_cast<size_t>(difference.first - core.begin()));
            fail(mismatch_reason(core, lean), input, core, lean);
        }
        if (expected && ((core[0] == 1) != expected->parses ||
                         (expected->parses && (core[1] == 1) != expected->checks))) {
            std::fprintf(stderr, "deterministic case: %s\n", expected->name.c_str());
            fail("deterministic case had an unexpected result", input, core, lean);
        }
    } catch (const std::exception& error) {
        if (expected) std::fprintf(stderr, "deterministic case: %s\n", expected->name.c_str());
        fail(error.what(), input);
    } catch (...) {
        if (expected) std::fprintf(stderr, "deterministic case: %s\n", expected->name.c_str());
        fail("unexpected native exception", input);
    }
}

void check_controls(bool large, const std::filesystem::path& corpus = {})
{
    const auto cases = transaction_cases::make_cases(large);
    if (!corpus.empty()) std::filesystem::create_directories(corpus);
    size_t rejected = 0, invalid = 0, valid = 0;
    for (const auto& test : cases) {
        compare_input(test.input, &test);
        if (!test.parses) ++rejected;
        else if (!test.checks) ++invalid;
        else ++valid;
        if (!corpus.empty()) {
            std::ofstream file(corpus / test.name, std::ios::binary);
            file.exceptions(std::ios::failbit | std::ios::badbit);
            file.write(reinterpret_cast<const char*>(test.input.data()), test.input.size());
        }
    }
    std::fprintf(stderr, "controls passed: %zu (%zu parse-reject, %zu check-reject, %zu check-pass)\n",
                 cases.size(), rejected, invalid, valid);
}

void replay_directory(const std::filesystem::path& path)
{
    std::vector<std::filesystem::path> inputs;
    for (const auto& entry : std::filesystem::directory_iterator(path)) {
        if (entry.is_regular_file()) inputs.push_back(entry.path());
    }
    std::sort(inputs.begin(), inputs.end());
    size_t count = 0;
    for (const auto& input_path : inputs) {
        std::ifstream file(input_path, std::ios::binary);
        if (!file) throw std::runtime_error("Cannot read replay input");
        const Bytes input{std::istreambuf_iterator<char>{file}, std::istreambuf_iterator<char>{}};
        if (file.bad()) throw std::runtime_error("Replay input read failed");
        std::fprintf(stderr, "replay: %s\n", input_path.filename().string().c_str());
        compare_input(input);
        ++count;
    }
    std::fprintf(stderr, "replay passed: %zu inputs\n", count);
}

} // namespace

// On macOS libFuzzer discovers optional callbacks with dlsym. Lean's native
// flags include -fvisibility=hidden, so explicitly export these entry points.
extern "C" __attribute__((visibility("default"))) int LLVMFuzzerInitialize(int* argc, char*** argv)
{
    initialize_lean();
    bool regression = false, large = false;
    std::filesystem::path corpus, replay;
    for (int i = 1; i < *argc; ++i) {
        const std::string_view arg{(*argv)[i]};
        if (arg == "--regression=small" || arg == "--regression=large") {
            regression = true;
            large = arg == "--regression=large";
        } else if (arg.starts_with("--write-corpus=")) {
            corpus = arg.substr(15);
        } else if (arg.starts_with("--replay=")) {
            replay = arg.substr(9);
        }
    }
    if (!corpus.empty() && !regression) {
        fail("--write-corpus requires --regression=small or large", {});
    }
    try {
        if (regression) check_controls(large, corpus);
        if (!replay.empty()) replay_directory(replay);
    } catch (const std::exception& error) {
        fail(error.what(), {});
    }
    if (regression || !replay.empty()) std::exit(0); // Exit before the fuzz engine starts.
    std::fprintf(stderr, "btc-verified: parsing, field, and context-free check comparisons enabled; "
                         "campaign size limit is controlled by libFuzzer -max_len\n");
    return 0;
}

extern "C" __attribute__((visibility("default"))) int LLVMFuzzerTestOneInput(
    const uint8_t* data, size_t size)
{
    initialize_lean();
    fuzz_executions.fetch_add(1, std::memory_order_relaxed);
    compare_input(Input{data, size});
    return 0;
}

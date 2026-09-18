// Independent wire fixtures for the context-free transaction contract.
// Expected verdicts come from the rules, never from querying either oracle.
// https://github.com/bitcoin/bitcoin/blob/fc6923cec5b440b611700f6629d8c6a61c6f11bd/src/consensus/tx_check.cpp#L19-L67
#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace transaction_cases {
using Bytes = std::vector<uint8_t>;
struct Case {
    std::string name;
    Bytes input;
    bool parses;
    bool checks;
};

inline void word(Bytes& bytes, uint64_t value, size_t width)
{
    for (size_t i = 0; i < width; ++i) bytes.push_back((value >> (8 * i)) & 0xff);
}

inline void count(Bytes& bytes, uint64_t value)
{
    if (value < 253) bytes.push_back(value);
    else if (value <= 0xffff) { bytes.push_back(253); word(bytes, value, 2); }
    else if (value <= 0xffffffff) { bytes.push_back(254); word(bytes, value, 4); }
    else { bytes.push_back(255); word(bytes, value, 8); }
}

inline void blob(Bytes& bytes, const Bytes& value)
{
    count(bytes, value.size());
    bytes.insert(bytes.end(), value.begin(), value.end());
}

inline Bytes input(uint8_t hash = 1, uint32_t index = 0, const Bytes& script = {},
                   uint32_t sequence = 0xffffffff)
{
    Bytes result(32, hash);
    word(result, index, 4);
    blob(result, script);
    word(result, sequence, 4);
    return result;
}

inline Bytes output(uint64_t amount = 0, const Bytes& script = {})
{
    Bytes result;
    word(result, amount, 8);
    blob(result, script);
    return result;
}

inline Bytes transaction(const std::vector<Bytes>& inputs, const std::vector<Bytes>& outputs,
                         const std::vector<std::vector<Bytes>>& witnesses = {},
                         uint32_t version = 1, uint32_t locktime = 0)
{
    Bytes result;
    word(result, version, 4);
    if (!witnesses.empty()) result.insert(result.end(), {0, 1});
    count(result, inputs.size());
    for (const auto& value : inputs) result.insert(result.end(), value.begin(), value.end());
    count(result, outputs.size());
    for (const auto& value : outputs) result.insert(result.end(), value.begin(), value.end());
    for (const auto& witness : witnesses) {
        count(result, witness.size());
        for (const auto& item : witness) blob(result, item);
    }
    word(result, locktime, 4);
    return result;
}

inline std::vector<Case> make_cases(bool large)
{
    constexpr uint64_t money = 21'000'000ULL * 100'000'000;
    std::vector<Case> cases;
    auto add = [&](std::string name, Bytes bytes, bool parses, bool checks) {
        cases.push_back({std::move(name), std::move(bytes), parses, checks});
    };
    const auto regular = transaction({input()}, {output()});
    const auto witnessed = transaction({input()}, {output()}, {{Bytes{0x80}}});
    add("regular", regular, true, true);
    add("empty-bytes", {}, false, false);
    add("empty-input-output", transaction({}, {}), true, false);
    add("empty-input-nonempty-output", transaction({}, {output()}), false, false);
    add("empty-output", transaction({input()}, {}), true, false);
    add("witness-empty-output", transaction({input()}, {}, {{Bytes{}}}), true, false);
    add("duplicate-inputs", transaction({input(), input()}, {output()}), true, false);
    add("nonadjacent-duplicate", transaction({input(), input(2), input()}, {output()}), true, false);
    add("same-hash-distinct-index", transaction({input(), input(1, 1)}, {output()}), true, true);
    add("same-index-distinct-hash", transaction({input(), input(2)}, {output()}), true, true);
    add("null-in-regular", transaction({input(), input(0, 0xffffffff)}, {output()}), true, false);
    add("zero-hash-not-null", transaction({input(0, 0)}, {output()}), true, true);
    add("max-index-not-null", transaction({input(1, 0xffffffff)}, {output()}), true, true);
    for (size_t length : {0, 1, 2, 100, 101}) {
        add("coinbase-script-" + std::to_string(length),
            transaction({input(0, 0xffffffff, Bytes(length, 0xff))}, {output()}),
            true, length >= 2 && length <= 100);
    }
    add("coinbase-empty-output", transaction({input(0, 0xffffffff, {0, 0})}, {}), true, false);
    add("coinbase-excess-money", transaction({input(0, 0xffffffff, {0, 0})}, {output(money + 1)}), true, false);
    add("coinbase-aggregate-excess", transaction({input(0, 0xffffffff, {0, 0})},
                                               {output(money), output(1)}), true, false);
    add("coinbase-negative", transaction({input(0, 0xffffffff, {0, 0})}, {output(UINT64_MAX)}), true, false);
    for (uint64_t amount : {uint64_t{0}, money, money + 1, uint64_t{INT64_MAX},
                            uint64_t{1} << 63, uint64_t{UINT64_MAX}}) {
        add("amount-" + std::to_string(amount), transaction({input()}, {output(amount)}), true, amount <= money);
    }
    add("sum-at-limit", transaction({input()}, {output(money - 1), output(1)}), true, true);
    add("sum-over-limit", transaction({input()}, {output(money), output(1)}), true, false);
    add("unsigned-field-boundaries", transaction({input(0x12, 0x89abcdef, {0x4c}, 0x87654321)},
        {output(0x010203040506ULL, {0x4d})}, {}, 0xfedcba98, 0xdeadbeef), true, true);
    add("scripts-not-tokenized", transaction({input(1, 0, {0x4e, 0xff})},
        {output(0, {0x4d, 0xff})}), true, true);
    add("witness", witnessed, true, true);
    add("witness-one-empty-item", transaction({input()}, {output()}, {{Bytes{}}}), true, true);
    add("witness-all-empty-stacks", transaction({input()}, {output()}, {{}}), false, false);
    add("witness-mixed-stacks", transaction({input(), input(2)}, {output()}, {{}, {Bytes{}}}), true, true);
    add("witness-duplicate-input", transaction({input(), input()}, {output()}, {{}, {Bytes{}}}), true, false);
    add("witness-coinbase", transaction({input(0, 0xffffffff, {0, 0})}, {output()}, {{Bytes(32, 0)}}), true, true);
    for (uint8_t flag : {2, 3, 0x80, 0xff}) {
        auto bytes = witnessed;
        bytes[5] = flag;
        add("unknown-flag-" + std::to_string(flag), std::move(bytes), false, false);
    }
    auto suffix = regular;
    suffix.insert(suffix.end(), {0xde, 0xad, 0xbe, 0xef});
    add("trailing-bytes", std::move(suffix), true, true);
    // Every strict prefix of these forms is incomplete, including field boundaries.
    for (size_t length = 0; length < witnessed.size(); ++length) {
        add("witness-prefix-" + std::to_string(length),
            Bytes(witnessed.begin(), witnessed.begin() + length), false, false);
    }
    for (size_t length = 0; length < regular.size(); ++length) {
        add("legacy-prefix-" + std::to_string(length),
            Bytes(regular.begin(), regular.begin() + length), false, false);
    }
    // Prefix positions in these deliberately small fixtures are fixed and independent
    // of the code under test. Replace each short CompactSize with a noncanonical form.
    for (const auto& [name, bytes, offsets] : std::vector<std::tuple<std::string, Bytes, std::vector<size_t>>>{
             {"legacy", regular, {4, 41, 46, 55}},
             {"witness", witnessed, {6, 43, 48, 57, 58, 59}}}) {
        for (size_t offset : offsets) {
            for (size_t width : {2, 4, 8}) {
                auto bad = bytes;
                Bytes replacement{static_cast<uint8_t>(width == 2 ? 253 : width == 4 ? 254 : 255)};
                word(replacement, bytes[offset], width);
                bad.erase(bad.begin() + offset);
                bad.insert(bad.begin() + offset, replacement.begin(), replacement.end());
                add(name + "-noncanonical-" + std::to_string(offset) + "-" + std::to_string(width),
                    std::move(bad), false, false);
            }
        }
    }
    for (size_t length : {252, 253}) {
        add("script-count-" + std::to_string(length),
            transaction({input(1, 0, Bytes(length, 0))}, {output(0, Bytes(length, 0))}), true, true);
        add("witness-count-" + std::to_string(length),
            transaction({input()}, {output()}, {std::vector<Bytes>(length, Bytes{})}), true, true);
        add("witness-item-length-" + std::to_string(length),
            transaction({input()}, {output()}, {{Bytes(length, 0)}}), true, true);
        add("output-count-" + std::to_string(length),
            transaction({input()}, std::vector<Bytes>(length, output())), true, true);
    }
    if (large) {
        for (size_t length : {4097, 65535, 65536}) {
            add("large-script-" + std::to_string(length),
                transaction({input()}, {output(0, Bytes(length, 0))}), true, true);
            add("large-witness-item-" + std::to_string(length),
                transaction({input()}, {output()}, {{Bytes(length, 0)}}), true, true);
        }
        // One-input/one-output base is 60 bytes; a script >=65536 adds four
        // CompactSize prefix bytes, so total stripped size = script length + 64.
        for (size_t size : {999999, 1000000, 1000001}) {
            auto bytes = transaction({input()}, {output(0, Bytes(size - 64, 0))});
            add("stripped-size-" + std::to_string(size), bytes, true, size <= 1000000);
            bytes.insert(bytes.end(), 4096, 0xff);
            add("stripped-size-with-suffix-" + std::to_string(size), std::move(bytes), true, size <= 1000000);
            // Coinbase has two more scriptSig bytes than the regular fixture.
            add("coinbase-stripped-size-" + std::to_string(size),
                transaction({input(0, 0xffffffff, {0, 0})}, {output(0, Bytes(size - 66, 0))}),
                true, size <= 1000000);
        }
        // CheckTransaction counts stripped bytes, not witness bytes or full block weight.
        add("witness-over-million", transaction({input()}, {output()}, {{Bytes(1000001, 0)}}), true, true);
        add("witness-over-four-million", transaction({input()}, {output()}, {{Bytes(4000001, 0)}}), true, true);
    }
    return cases;
}
} // namespace transaction_cases

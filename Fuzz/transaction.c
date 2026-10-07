/* Differential public-ABI observations, not a proof of Core equivalence.
 * No btck symbol is linked globally: each provider owns its handles and calls.
 * Load instrumented libraries before libFuzzer initializes its coverage map;
 * never unload Lean's process-lifetime runtime or module constants.
 */
#include <bitcoinkernel.h>
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define KERNEL_SYMBOLS(X) \
    X(btck_transaction_create) \
    X(btck_transaction_copy) \
    X(btck_transaction_destroy) \
    X(btck_transaction_to_bytes) \
    X(btck_transaction_check) \
    X(btck_tx_validation_state_create) \
    X(btck_tx_validation_state_destroy) \
    X(btck_tx_validation_state_get_validation_mode) \
    X(btck_tx_validation_state_get_tx_validation_result)

struct provider {
    void* library;
#define DECLARE(name) __typeof__(&name) name;
    KERNEL_SYMBOLS(DECLARE)
#undef DECLARE
};

struct buffer {
    unsigned char* data;
    size_t size;
    size_t capacity;
};

struct observation {
    int parsed;
    int serialization;
    int verdict;
    btck_ValidationMode mode;
    btck_TxValidationResult result;
    struct buffer bytes;
};

static struct provider core, verified;
static const char* artifact_directory;
static int inject_mismatch;

/* Version 1, no inputs, no outputs, locktime 0: both providers parse this
 * transaction but reject it during context-free checking. Priming a reused
 * state with it exercises the API's requirement that each later check replace
 * the complete prior result.
 */
static const uint8_t empty_transaction[] = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0};

static _Noreturn void infrastructure(const char* message)
{
    fprintf(stderr, "infrastructure error: %s\n", message);
    exit(2);
}

static struct provider load_provider(const char* path)
{
    struct provider api = {.library = dlopen(path, RTLD_NOW | RTLD_LOCAL)};
    if (api.library == NULL) infrastructure(dlerror());
#define LOAD(name) \
    api.name = (__typeof__(api.name))dlsym(api.library, #name); \
    if (api.name == NULL) infrastructure("missing symbol: " #name);
    KERNEL_SYMBOLS(LOAD)
#undef LOAD
    return api;
}

int LLVMFuzzerInitialize(int* argc, char*** argv)
{
    const char* core_path = NULL;
    const char* verified_path = NULL;
    int kept = 1;
    for (int i = 1; i < *argc; ++i) {
        const char* argument = (*argv)[i];
        if (strncmp(argument, "--core=", 7) == 0) core_path = argument + 7;
        else if (strncmp(argument, "--verified=", 11) == 0) verified_path = argument + 11;
        else if (strncmp(argument, "--artifacts=", 12) == 0) artifact_directory = argument + 12;
        else if (strcmp(argument, "--inject-mismatch") == 0) inject_mismatch = 1;
        else (*argv)[kept++] = (*argv)[i];
    }
    (*argv)[kept] = NULL;
    *argc = kept;
    if (!core_path || !*core_path || !verified_path || !*verified_path ||
        !artifact_directory || !*artifact_directory)
        infrastructure("require --core=PATH --verified=PATH --artifacts=DIR");
    core = load_provider(core_path);
    verified = load_provider(verified_path);
#define DISTINCT(name) \
    if (core.name == verified.name) infrastructure("providers share symbol: " #name);
    KERNEL_SYMBOLS(DISTINCT)
#undef DISTINCT
    return 0;
}

/* Copy each borrowed callback chunk; geometric growth avoids quadratic copies.
 * Our allocation failures are infrastructure failures, never verdict evidence.
 */
static int collect_bytes(const void* bytes, size_t size, void* context)
{
    struct buffer* output = context;
    if (size > SIZE_MAX - output->size) infrastructure("serialization size overflow");
    const size_t needed = output->size + size;
    if (needed > output->capacity) {
        size_t capacity = output->capacity ? output->capacity : 256;
        while (capacity < needed) {
            if (capacity > SIZE_MAX / 2) {
                capacity = needed;
                break;
            }
            capacity *= 2;
        }
        unsigned char* grown = realloc(output->data, capacity);
        if (grown == NULL) infrastructure("serialization allocation failed");
        output->data = grown;
        output->capacity = capacity;
    }
    if (size != 0) memcpy(output->data + output->size, bytes, size);
    output->size = needed;
    return 0;
}

/* Run exactly the same public operations for both providers. A null create is
 * API-level parse rejection; this API cannot diagnose its allocation failures.
 */
static struct observation observe(const struct provider* api,
                                  const uint8_t* input, size_t size)
{
    struct observation output = {.serialization = -1, .verdict = -1};
    btck_Transaction* original = api->btck_transaction_create(input, size);
    if (original == NULL) return output;
    output.parsed = 1;
    btck_Transaction* tx = api->btck_transaction_copy(original);
    if (tx == NULL) infrastructure("transaction copy failed");
    api->btck_transaction_destroy(original);
    btck_TxValidationState* state = api->btck_tx_validation_state_create();
    if (state == NULL) infrastructure("validation state allocation failed");
    btck_Transaction* prior = api->btck_transaction_create(
        empty_transaction, sizeof(empty_transaction));
    if (prior == NULL) infrastructure("state-primer transaction did not parse");
    (void)api->btck_transaction_check(prior, state);
    api->btck_transaction_destroy(prior);
    output.serialization = api->btck_transaction_to_bytes(tx, collect_bytes, &output.bytes);
    output.verdict = api->btck_transaction_check(tx, state);
    output.mode = api->btck_tx_validation_state_get_validation_mode(state);
    output.result = api->btck_tx_validation_state_get_tx_validation_result(state);
    api->btck_tx_validation_state_destroy(state);
    api->btck_transaction_destroy(tx);
    return output;
}

static const char* difference(const struct observation* left,
                              const struct observation* right)
{
    if (left->parsed != right->parsed) return "parse acceptance";
    if (!left->parsed) return NULL;
    if (left->serialization != right->serialization) return "serialization status";
    if (left->bytes.size != right->bytes.size ||
        (left->bytes.size && memcmp(left->bytes.data, right->bytes.data, left->bytes.size)))
        return "canonical bytes";
    if (left->verdict != right->verdict) return "check verdict";
    if (left->mode != right->mode) return "validation mode";
    if (left->result != right->result) return "validation result";
    return NULL;
}

static void write_artifact(const char* name, const void* bytes, size_t size)
{
    char path[4096];
    const int length = snprintf(path, sizeof(path), "%s/%s", artifact_directory, name);
    if (length < 0 || (size_t)length >= sizeof(path)) infrastructure("artifact path too long");
    FILE* file = fopen(path, "wb");
    if (file == NULL) infrastructure("cannot open artifact file");
    if (size != 0 && fwrite(bytes, 1, size, file) != size)
        infrastructure("cannot write artifact file");
    if (fclose(file) != 0) infrastructure("cannot close artifact file");
}

static void write_observation(const char* metadata_name, const char* bytes_name,
                              const struct observation* output)
{
    char metadata[256];
    const int size = snprintf(metadata, sizeof(metadata),
        "parsed=%d\nserialization=%d\nverdict=%d\nmode=%u\nresult=%u\nbytes=%zu\n",
        output->parsed, output->serialization, output->verdict,
        (unsigned)output->mode, (unsigned)output->result, output->bytes.size);
    if (size < 0 || (size_t)size >= sizeof(metadata)) infrastructure("observation too long");
    write_artifact(metadata_name, metadata, (size_t)size);
    write_artifact(bytes_name, output->bytes.data, output->bytes.size);
}

int LLVMFuzzerTestOneInput(const uint8_t* input, size_t size)
{
    struct observation core_output = observe(&core, input, size);
    struct observation verified_output = observe(&verified, input, size);
    /* Change only a completed observation, never either provider's execution. */
    if (inject_mismatch && verified_output.parsed) {
        verified_output.verdict = !verified_output.verdict;
        fprintf(stderr, "injected mismatch: verified check verdict\n");
    }
    const char* category = difference(&core_output, &verified_output);
    if (category != NULL) {
        write_artifact("mismatch.input", input, size);
        write_observation("core.txt", "core.bytes", &core_output);
        write_observation("verified.txt", "verified.bytes", &verified_output);
        fprintf(stderr, "conformance mismatch: %s\n", category);
    }
    free(core_output.bytes.data);
    free(verified_output.bytes.data);
    /* Provider crashes never reach this comparison or acquire its label. */
    if (category != NULL) {
        fflush(stderr);
        abort();
    }
    return 0;
}

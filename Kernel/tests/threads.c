#include <kernel/bitcoinkernel.h>

#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum { THREAD_COUNT = 16 };

static const unsigned char LEGACY_TX[] = {
    0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
    0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
    0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e,
    0x1f, 0x03, 0x00, 0x00, 0x00, 0x03, 0xaa, 0xbb, 0xcc, 0xfe, 0xff, 0xff,
    0xff, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
    0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x6a, 0x00, 0x44,
    0x33, 0x22, 0x11,
};

static const unsigned char LEGACY_TXID[] = {
    0xce, 0xa8, 0x7c, 0x70, 0xf8, 0x83, 0x93, 0xfa, 0xd0, 0x9f, 0x4d, 0x61,
    0x03, 0x70, 0xca, 0xc8, 0xca, 0xd0, 0x22, 0x1b, 0x60, 0xe5, 0xc9, 0xbc,
    0xee, 0xa8, 0x77, 0xe3, 0xde, 0x5d, 0x4a, 0x3b,
};

static atomic_uint failures = ATOMIC_VAR_INIT(0);
static pthread_mutex_t failure_mutex = PTHREAD_MUTEX_INITIALIZER;

static void expect_impl(int condition, const char* expression, size_t worker)
{
    if (condition) return;
    atomic_fetch_add_explicit(&failures, 1, memory_order_relaxed);
    (void)pthread_mutex_lock(&failure_mutex);
    fprintf(stderr, "worker %zu: requirement failed: %s\n", worker, expression);
    (void)pthread_mutex_unlock(&failure_mutex);
}

#define EXPECT(worker, condition) expect_impl((condition), #condition, (worker))

static void report_pthread_failure(const char* operation, int error, size_t worker)
{
    atomic_fetch_add_explicit(&failures, 1, memory_order_relaxed);
    (void)pthread_mutex_lock(&failure_mutex);
    if (worker < THREAD_COUNT) {
        fprintf(stderr, "worker %zu: %s failed: %s\n", worker, operation, strerror(error));
    } else {
        fprintf(stderr, "thread harness: %s failed: %s\n", operation, strerror(error));
    }
    (void)pthread_mutex_unlock(&failure_mutex);
}

static unsigned int failure_count(void)
{
    return atomic_load_explicit(&failures, memory_order_relaxed);
}

struct start_gate {
    size_t participants;
    size_t arrived;
    int open;
    pthread_mutex_t mutex;
    pthread_cond_t condition;
};

static int start_gate_init(struct start_gate* gate, size_t participants)
{
    int error;

    gate->participants = participants;
    gate->arrived = 0;
    gate->open = 0;
    error = pthread_mutex_init(&gate->mutex, NULL);
    if (error != 0) {
        report_pthread_failure("pthread_mutex_init", error, THREAD_COUNT);
        return 0;
    }
    error = pthread_cond_init(&gate->condition, NULL);
    if (error != 0) {
        report_pthread_failure("pthread_cond_init", error, THREAD_COUNT);
        (void)pthread_mutex_destroy(&gate->mutex);
        return 0;
    }
    return 1;
}

static void start_gate_abort(struct start_gate* gate)
{
    int error = pthread_mutex_lock(&gate->mutex);
    if (error != 0) {
        report_pthread_failure("pthread_mutex_lock", error, THREAD_COUNT);
        return;
    }
    gate->open = 1;
    error = pthread_cond_broadcast(&gate->condition);
    if (error != 0) {
        report_pthread_failure("pthread_cond_broadcast", error, THREAD_COUNT);
    }
    error = pthread_mutex_unlock(&gate->mutex);
    if (error != 0) {
        report_pthread_failure("pthread_mutex_unlock", error, THREAD_COUNT);
    }
}

static int start_gate_arrive_and_wait(struct start_gate* gate, size_t worker)
{
    int error = pthread_mutex_lock(&gate->mutex);
    int success = 1;

    if (error != 0) {
        report_pthread_failure("pthread_mutex_lock", error, worker);
        return 0;
    }

    ++gate->arrived;
    if (gate->arrived == gate->participants) {
        gate->open = 1;
        error = pthread_cond_broadcast(&gate->condition);
        if (error != 0) {
            report_pthread_failure("pthread_cond_broadcast", error, worker);
            success = 0;
        }
    } else {
        while (!gate->open) {
            error = pthread_cond_wait(&gate->condition, &gate->mutex);
            if (error != 0) {
                report_pthread_failure("pthread_cond_wait", error, worker);
                success = 0;
                break;
            }
        }
    }

    error = pthread_mutex_unlock(&gate->mutex);
    if (error != 0) {
        report_pthread_failure("pthread_mutex_unlock", error, worker);
        success = 0;
    }
    return success;
}

static void start_gate_destroy(struct start_gate* gate)
{
    int error = pthread_cond_destroy(&gate->condition);
    if (error != 0) {
        report_pthread_failure("pthread_cond_destroy", error, THREAD_COUNT);
    }
    error = pthread_mutex_destroy(&gate->mutex);
    if (error != 0) {
        report_pthread_failure("pthread_mutex_destroy", error, THREAD_COUNT);
    }
}

typedef void (*worker_function)(size_t worker, void* context);

struct worker_start {
    size_t worker;
    worker_function function;
    void* context;
    struct start_gate* gate;
};

static void* thread_entry(void* argument)
{
    struct worker_start* start = argument;
    if (start->gate != NULL &&
        !start_gate_arrive_and_wait(start->gate, start->worker)) {
        return NULL;
    }
    start->function(start->worker, start->context);
    return NULL;
}

static int run_threads(worker_function function, void* context, int synchronize)
{
    pthread_t threads[THREAD_COUNT];
    struct worker_start starts[THREAD_COUNT];
    struct start_gate gate;
    struct start_gate* gate_pointer = NULL;
    size_t created = 0;
    int complete = 1;

    if (synchronize) {
        if (!start_gate_init(&gate, THREAD_COUNT)) return 0;
        gate_pointer = &gate;
    }

    for (size_t i = 0; i < THREAD_COUNT; ++i) {
        starts[i].worker = i;
        starts[i].function = function;
        starts[i].context = context;
        starts[i].gate = gate_pointer;
        const int error = pthread_create(&threads[i], NULL, thread_entry, &starts[i]);
        if (error != 0) {
            report_pthread_failure("pthread_create", error, i);
            complete = 0;
            break;
        }
        ++created;
    }

    if (created != THREAD_COUNT && gate_pointer != NULL) {
        start_gate_abort(gate_pointer);
    }
    for (size_t i = 0; i < created; ++i) {
        const int error = pthread_join(threads[i], NULL);
        if (error != 0) {
            report_pthread_failure("pthread_join", error, i);
            complete = 0;
        }
    }
    if (gate_pointer != NULL) start_gate_destroy(gate_pointer);
    return complete && created == THREAD_COUNT;
}

struct lifecycle {
    btck_Transaction* originals[THREAD_COUNT];
    btck_Transaction* copies[THREAD_COUNT];
    btck_Transaction* shared_copies[THREAD_COUNT];
    btck_TransactionInput* input_copies[THREAD_COUNT];
    btck_TxValidationState* states[THREAD_COUNT];
};

static void first_use_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    lifecycle->originals[worker] = btck_transaction_create(LEGACY_TX, sizeof(LEGACY_TX));
    lifecycle->states[worker] = btck_tx_validation_state_create();
    EXPECT(worker, lifecycle->originals[worker] != NULL);
    EXPECT(worker, lifecycle->states[worker] != NULL);
    if (lifecycle->originals[worker] != NULL) {
        EXPECT(worker, btck_transaction_count_inputs(lifecycle->originals[worker]) == 1);
        EXPECT(worker, btck_transaction_count_outputs(lifecycle->originals[worker]) == 2);
    }
}

static void copy_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    lifecycle->copies[worker] =
        btck_transaction_copy(lifecycle->originals[(worker + 1) % THREAD_COUNT]);
    lifecycle->shared_copies[worker] = btck_transaction_copy(lifecycle->originals[0]);
    EXPECT(worker, lifecycle->copies[worker] != NULL);
    EXPECT(worker, lifecycle->shared_copies[worker] != NULL);
}

static void destroy_original_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    const size_t target = (worker + 3) % THREAD_COUNT;
    btck_transaction_destroy(lifecycle->originals[target]);
    lifecycle->originals[target] = NULL;
}

static void getter_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    const btck_Txid* txid = btck_transaction_get_txid(lifecycle->shared_copies[worker]);
    unsigned char bytes[32] = {0};

    EXPECT(worker, txid != NULL);
    if (txid != NULL) {
        btck_txid_to_bytes(txid, bytes);
        EXPECT(worker, memcmp(bytes, LEGACY_TXID, sizeof(bytes)) == 0);
    }

    EXPECT(worker, btck_transaction_check(lifecycle->copies[worker],
                                           lifecycle->states[worker]) == 1);
    EXPECT(worker,
           btck_tx_validation_state_get_validation_mode(lifecycle->states[worker]) ==
               btck_ValidationMode_VALID);
    const btck_TransactionInput* input =
        btck_transaction_get_input_at(lifecycle->copies[worker], 0);
    EXPECT(worker, input != NULL);
    if (input != NULL) {
        lifecycle->input_copies[worker] = btck_transaction_input_copy(input);
    }
    EXPECT(worker, lifecycle->input_copies[worker] != NULL);
}

static void destroy_handles_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    const size_t copy_target = (worker + 5) % THREAD_COUNT;
    const size_t shared_target = (worker + 7) % THREAD_COUNT;
    const size_t state_target = (worker + 9) % THREAD_COUNT;

    btck_transaction_destroy(lifecycle->copies[copy_target]);
    btck_transaction_destroy(lifecycle->shared_copies[shared_target]);
    btck_tx_validation_state_destroy(lifecycle->states[state_target]);
    lifecycle->copies[copy_target] = NULL;
    lifecycle->shared_copies[shared_target] = NULL;
    lifecycle->states[state_target] = NULL;
}

static void use_input_copy_worker(size_t worker, void* context)
{
    struct lifecycle* lifecycle = context;
    const size_t target = (worker + 11) % THREAD_COUNT;
    const btck_TransactionOutPoint* outpoint;

    EXPECT(worker, btck_transaction_input_get_sequence(lifecycle->input_copies[target]) ==
                       UINT32_C(0xfffffffe));
    outpoint = btck_transaction_input_get_out_point(lifecycle->input_copies[target]);
    EXPECT(worker, outpoint != NULL);
    if (outpoint != NULL) {
        EXPECT(worker, btck_transaction_out_point_get_index(outpoint) == 3);
    }
    btck_transaction_input_destroy(lifecycle->input_copies[target]);
    lifecycle->input_copies[target] = NULL;
}

static void cleanup_lifecycle(struct lifecycle* lifecycle)
{
    for (size_t i = 0; i < THREAD_COUNT; ++i) {
        btck_transaction_destroy(lifecycle->originals[i]);
        btck_transaction_destroy(lifecycle->copies[i]);
        btck_transaction_destroy(lifecycle->shared_copies[i]);
        btck_transaction_input_destroy(lifecycle->input_copies[i]);
        btck_tx_validation_state_destroy(lifecycle->states[i]);
        lifecycle->originals[i] = NULL;
        lifecycle->copies[i] = NULL;
        lifecycle->shared_copies[i] = NULL;
        lifecycle->input_copies[i] = NULL;
        lifecycle->states[i] = NULL;
    }
}

int main(void)
{
    struct lifecycle lifecycle = {0};

    // No caller-side Lean initialization is permitted. These are the first
    // library calls in this fresh process and deliberately race runtime
    // registration, parsing, and eager txid computation.
    if (!run_threads(first_use_worker, &lifecycle, 1) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    // New threads copy handles created by the first thread pool. The shared
    // copies are logical references to one immutable transaction payload.
    if (!run_threads(copy_worker, &lifecycle, 0) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    // Destroy every original through a different array index permutation.
    if (!run_threads(destroy_original_worker, &lifecycle, 0) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    // Exercise simultaneous read-only access through shared references after
    // the original transaction references have been released.
    if (!run_threads(getter_worker, &lifecycle, 1) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    // A third thread pool releases transaction and state references. The
    // independently owned input snapshots must remain valid afterward.
    if (!run_threads(destroy_handles_worker, &lifecycle, 0) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    if (!run_threads(use_input_copy_worker, &lifecycle, 0) || failure_count() != 0) {
        cleanup_lifecycle(&lifecycle);
        return 1;
    }

    cleanup_lifecycle(&lifecycle);
    puts("btc-verified kernel threaded lifecycle tests passed");
    return 0;
}

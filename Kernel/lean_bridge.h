/* Private C declarations for exports generated from Kernel/Transaction.lean.
 * bitcoinkernel.c includes this header; external clients and the native tests
 * include only the upstream bitcoinkernel.h and never manipulate Lean objects.
 *
 * Generated @[export] wrappers consume object arguments; object results are
 * owned. Passing an object transfers a reference, so reusing a borrowed
 * object requires an increment first. The adapter retains the decoded Tx as
 * the public handle and supplies temporary references to encode and check,
 * so those consuming exports do not consume the caller's handle.
 * The build checks these declarations against generated C for the pinned
 * toolchain; this is not a second public API or a proof of C memory safety.
 */
#ifndef BTC_VERIFIED_KERNEL_LEAN_BRIDGE_H
#define BTC_VERIFIED_KERNEL_LEAN_BRIDGE_H

#include <lean/lean.h>

void lean_initialize(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_obj_res initialize_btc_x2dverified_Kernel_Transaction(uint8_t builtin);

lean_obj_res btcv_kernel_decode(lean_obj_arg bytes);
lean_obj_res btcv_kernel_encode(lean_obj_arg transaction);
uint8_t btcv_kernel_check(lean_obj_arg transaction);

#endif

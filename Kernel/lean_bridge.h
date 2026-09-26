/* Private declarations for the pinned Lean toolchain, not a public header.
 * Generated @[export] wrappers consume object arguments and return owned objects.
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

// Private interface to the generated Lean code. Not installed or exported.
// @[export] consumes its object arguments even when inference borrows internally.
#ifndef BTC_VERIFIED_KERNEL_LEAN_BRIDGE_H
#define BTC_VERIFIED_KERNEL_LEAN_BRIDGE_H

#include <lean/lean.h>

void lean_initialize(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_obj_res initialize_btc_x2dverified_Kernel_Transaction(uint8_t builtin);

lean_obj_res btcv_kernel_decode(lean_obj_arg input);
lean_obj_res btcv_kernel_encode(lean_obj_arg tx);
lean_obj_res btcv_kernel_encode_stripped(lean_obj_arg tx);
uint8_t btcv_kernel_check(lean_obj_arg tx);
uint32_t btcv_kernel_locktime(lean_obj_arg tx);
lean_obj_res btcv_kernel_inputs(lean_obj_arg tx);
lean_obj_res btcv_kernel_outputs(lean_obj_arg tx);
lean_obj_res btcv_kernel_witnesses(lean_obj_arg tx);
lean_obj_res btcv_kernel_input_txid(lean_obj_arg input);
uint32_t btcv_kernel_input_index(lean_obj_arg input);
uint32_t btcv_kernel_input_sequence(lean_obj_arg input);
lean_obj_res btcv_kernel_input_script(lean_obj_arg input);
uint64_t btcv_kernel_output_amount(lean_obj_arg output);
lean_obj_res btcv_kernel_output_script(lean_obj_arg output);
lean_obj_res btcv_kernel_hash(lean_obj_arg bytes);
#endif

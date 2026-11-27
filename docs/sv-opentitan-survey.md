# OpenTitan primitive and small-IP survey

Pinned source: `lowRISC/opentitan` at commit `7948d2088be5b63d068c43b7ba02c84d58fff7ce` from `https://github.com/lowRISC/opentitan.git`. The checkout was fetched outside this repository. Its top-level `LICENSE` is Apache-2.0. The survey date is 2026-11-27.

The survey covers every module Slang exposes from `hw/ip/prim/rtl/*.sv` and the available RTL directories for `uart`, `spi_host`, `spi_device`, `i2c`, `gpio`, `rv_timer`, `aon_timer`, and `pwm`. Each source was extracted with the approved Slang frontend, loaded through the ordinary `load_design_sv2` admission path, and, when admitted, given one empty-input `CoreMemDesign.step` call. Sources that timed out during extraction remain explicit rows. No source was changed and no simulator result is claimed by this survey.

## Counts

| outcome | count |
| --- | ---: |
| modules surveyed | 206 |
| extracts | 206 |
| ordinary loads | 58 |
| one-cycle steps | 56 |
| profile admitted | 56 |

Refusal families are counted by the first ordinary-route diagnostic.

| family | count |
| --- | ---: |
| constant evaluation | 41 |
| event scheduling | 3 |
| generate parameter | 2 |
| initial-state | 2 |
| module member Division | 1 |
| module member PortSymbol | 13 |
| module member Remainder | 2 |
| module member SlangError | 8 |
| module member SubroutineSymbol | 4 |
| module member TypeParameterSymbol | 1 |
| module member UninstantiatedDefSymbol | 17 |
| module member VariableSymbol | 1 |
| net metadata | 1 |
| parameter arity | 44 |
| scheduling | 10 |

## Module rows

| area | module | source | extracts | loads | one cycle | profile | first refusal |
| --- | --- | --- | :---: | :---: | :---: | :---: | --- |
| aon_timer | `aon_timer` | `hw/ip/aon_timer/rtl/aon_timer.sv` | YES | NO | NO | NO | parameter arity: got 0, want 5 |
| aon_timer | `aon_timer_core` | `hw/ip/aon_timer/rtl/aon_timer_core.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (lc_escalate_en_i) |
| aon_timer | `aon_timer_reg_top` | `hw/ip/aon_timer/rtl/aon_timer_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| i2c | `i2c` | `hw/ip/i2c/rtl/i2c.sv` | YES | NO | NO | NO | parameter arity: got 0, want 6 |
| i2c | `i2c_bus_monitor` | `hw/ip/i2c/rtl/i2c_bus_monitor.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| i2c | `i2c_controller_fsm` | `hw/ip/i2c/rtl/i2c_controller_fsm.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| i2c | `i2c_core` | `hw/ip/i2c/rtl/i2c_core.sv` | YES | NO | NO | NO | localparam 'FifoDepthW': unsupported node 'InvalidExpression' in a constant context |
| i2c | `i2c_fifo_sync_sram_adapter` | `hw/ip/i2c/rtl/i2c_fifo_sync_sram_adapter.sv` | YES | NO | NO | NO | localparam 'DepthW': unsupported node 'InvalidExpression' in a constant context |
| i2c | `i2c_fifos` | `hw/ip/i2c/rtl/i2c_fifos.sv` | YES | NO | NO | NO | localparam 'FifoDepthW': unsupported node 'InvalidExpression' in a constant context |
| i2c | `i2c_reg_top` | `hw/ip/i2c/rtl/i2c_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| i2c | `i2c_target_fsm` | `hw/ip/i2c/rtl/i2c_target_fsm.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_alert_receiver` | `hw/ip/prim/rtl/prim_alert_receiver.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (init_trig_i) |
| prim | `prim_alert_sender` | `hw/ip/prim/rtl/prim_alert_sender.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_alert_to_diff` | `hw/ip/prim/rtl/prim_alert_to_diff.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (alert_rx_o) |
| prim | `prim_arbiter_fixed` | `hw/ip/prim/rtl/prim_arbiter_fixed.sv` | YES | YES | NO | NO | GenerateDecl:instance-name: a declaration inside generate-if nested in generate-for has a template instance name; per-instance scope naming is not modeled (IEEE 1800-2023 §§27.4-27.6) |
| prim | `prim_arbiter_ppc` | `hw/ip/prim/rtl/prim_arbiter_ppc.sv` | YES | NO | NO | NO | localparam 'IdxW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_arbiter_tree` | `hw/ip/prim/rtl/prim_arbiter_tree.sv` | YES | YES | NO | NO | GenerateDecl:instance-name: a declaration inside generate-if nested in generate-for has a template instance name; per-instance scope naming is not modeled (IEEE 1800-2023 §§27.4-27.6) |
| prim | `prim_arbiter_tree_dup` | `hw/ip/prim/rtl/prim_arbiter_tree_dup.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'VariableSymbol:type' (arb_output_buf) |
| prim | `prim_ascon_duplex` | `hw/ip/prim/rtl/prim_ascon_duplex.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (ascon_variant) |
| prim | `prim_ascon_round` | `hw/ip/prim/rtl/prim_ascon_round.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_ascon_round.sv:37: unknown module 'prim_ascon_sbox') |
| prim | `prim_ascon_sbox` | `hw/ip/prim/rtl/prim_ascon_sbox.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_blanker` | `hw/ip/prim/rtl/prim_blanker.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_blank_and ( |
| prim | `prim_cdc_rand_delay` | `hw/ip/prim/rtl/prim_cdc_rand_delay.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_clock_gating_sync` | `hw/ip/prim/rtl/prim_clock_gating_sync.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (i_sync ( |
| prim | `prim_clock_meas` | `hw/ip/prim/rtl/prim_clock_meas.sv` | YES | NO | NO | NO | localparam 'CntWidth': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_clock_timeout` | `hw/ip/prim/rtl/prim_clock_timeout.sv` | YES | NO | NO | NO | localparam 'CntWidth': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_count` | `hw/ip/prim/rtl/prim_count.sv` | YES | NO | NO | NO | parameter arity: got 0, want 5 |
| prim | `prim_crc32` | `hw/ip/prim/rtl/prim_crc32.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_diff_decode` | `hw/ip/prim/rtl/prim_diff_decode.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_diff_decode.sv:217: unknown module 'prim_xnor2') |
| prim | `prim_diff_encode` | `hw/ip/prim/rtl/prim_diff_encode.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_prim_buf_in_req ( |
| prim | `prim_diff_to_alert` | `hw/ip/prim/rtl/prim_diff_to_alert.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (alert_rx_i) |
| prim | `prim_dom_and_2share` | `hw/ip/prim/rtl/prim_dom_and_2share.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_prim_xor_t01 ( |
| prim | `prim_double_lfsr` | `hw/ip/prim/rtl/prim_double_lfsr.sv` | YES | NO | NO | NO | parameter arity: got 0, want 13 |
| prim | `prim_edge_detector` | `hw/ip/prim/rtl/prim_edge_detector.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_edge_detector.sv:31: unknown module 'prim_flop_2sync') |
| prim | `prim_edn_req` | `hw/ip/prim/rtl/prim_edn_req.sv` | YES | NO | NO | NO | localparam 'SyncWidth': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_esc_receiver` | `hw/ip/prim/rtl/prim_esc_receiver.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_esc_sender` | `hw/ip/prim/rtl/prim_esc_sender.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (esc_rx_i) |
| prim | `prim_fifo_async` | `hw/ip/prim/rtl/prim_fifo_async.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (sync_wptr ( |
| prim | `prim_fifo_async_simple` | `hw/ip/prim/rtl/prim_fifo_async_simple.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_fifo_async_sram_adapter` | `hw/ip/prim/rtl/prim_fifo_async_sram_adapter.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_fifo_sync` | `hw/ip/prim/rtl/prim_fifo_sync.sv` | YES | NO | NO | NO | localparam 'DepthW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_fifo_sync_cnt` | `hw/ip/prim/rtl/prim_fifo_sync_cnt.sv` | YES | NO | NO | NO | localparam 'PtrW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_fifo_sync_redundant` | `hw/ip/prim/rtl/prim_fifo_sync_redundant.sv` | YES | NO | NO | NO | localparam 'DepthW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_filter` | `hw/ip/prim/rtl/prim_filter.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_filter_ctr` | `hw/ip/prim/rtl/prim_filter_ctr.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_flop_x` | `hw/ip/prim/rtl/prim_flop_x.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_flop_x.sv:28: unknown module 'prim_flop_en') |
| prim | `prim_gate_gen` | `hw/ip/prim/rtl/prim_gate_gen.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'Division:invalid-compilation' (frontend rejected source containing division) |
| prim | `prim_gf_mult` | `hw/ip/prim/rtl/prim_gf_mult.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SubroutineSymbol:Subroutine' (// GF(2^Width) * x |
| prim | `prim_hpc2` | `hw/ip/prim/rtl/prim_hpc2.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_prim_flop_x_y_masked ( |
| prim | `prim_hpc3` | `hw/ip/prim/rtl/prim_hpc3.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_prim_flop_x_y_masked ( |
| prim | `prim_intr_hw` | `hw/ip/prim/rtl/prim_intr_hw.sv` | YES | NO | NO | NO | generate if: unbound parameter 'IntrT' |
| prim | `prim_keccak` | `hw/ip/prim/rtl/prim_keccak.sv` | YES | NO | NO | NO | localparam 'RhoOffset': unsupported node 'AssignmentPattern:default-point' in a constant context |
| prim | `prim_lc_and_hardened` | `hw/ip/prim/rtl/prim_lc_and_hardened.sv` | YES | NO | NO | NO | parameter arity: got 0, want 1 |
| prim | `prim_lc_combine` | `hw/ip/prim/rtl/prim_lc_combine.sv` | YES | NO | NO | NO | localparam 'ActiveValue': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_lc_dec` | `hw/ip/prim/rtl/prim_lc_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_lc_or_hardened` | `hw/ip/prim/rtl/prim_lc_or_hardened.sv` | YES | NO | NO | NO | parameter arity: got 0, want 1 |
| prim | `prim_lc_sender` | `hw/ip/prim/rtl/prim_lc_sender.sv` | YES | NO | NO | NO | localparam 'ResetValue': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_lc_sync` | `hw/ip/prim/rtl/prim_lc_sync.sv` | YES | NO | NO | NO | localparam 'LcResetValue': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_leading_one_ppc` | `hw/ip/prim/rtl/prim_leading_one_ppc.sv` | YES | NO | NO | NO | localparam 'IdxW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_lfsr` | `hw/ip/prim/rtl/prim_lfsr.sv` | YES | NO | NO | NO | parameter arity: got 0, want 12 |
| prim | `prim_max_tree` | `hw/ip/prim/rtl/prim_max_tree.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SubroutineSymbol:Subroutine' (//////////////// |
| prim | `prim_msb_extend` | `hw/ip/prim/rtl/prim_msb_extend.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_mubi12_dec` | `hw/ip/prim/rtl/prim_mubi12_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi12_sender` | `hw/ip/prim/rtl/prim_mubi12_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi12_sync` | `hw/ip/prim/rtl/prim_mubi12_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi16_dec` | `hw/ip/prim/rtl/prim_mubi16_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi16_sender` | `hw/ip/prim/rtl/prim_mubi16_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi16_sync` | `hw/ip/prim/rtl/prim_mubi16_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi20_dec` | `hw/ip/prim/rtl/prim_mubi20_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi20_sender` | `hw/ip/prim/rtl/prim_mubi20_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi20_sync` | `hw/ip/prim/rtl/prim_mubi20_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi24_dec` | `hw/ip/prim/rtl/prim_mubi24_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi24_sender` | `hw/ip/prim/rtl/prim_mubi24_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi24_sync` | `hw/ip/prim/rtl/prim_mubi24_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi28_dec` | `hw/ip/prim/rtl/prim_mubi28_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi28_sender` | `hw/ip/prim/rtl/prim_mubi28_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi28_sync` | `hw/ip/prim/rtl/prim_mubi28_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi32_dec` | `hw/ip/prim/rtl/prim_mubi32_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi32_sender` | `hw/ip/prim/rtl/prim_mubi32_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi32_sync` | `hw/ip/prim/rtl/prim_mubi32_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi4_dec` | `hw/ip/prim/rtl/prim_mubi4_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi4_sender` | `hw/ip/prim/rtl/prim_mubi4_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi4_sync` | `hw/ip/prim/rtl/prim_mubi4_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_mubi8_dec` | `hw/ip/prim/rtl/prim_mubi8_dec.sv` | YES | NO | NO | NO | generate bound: unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_mubi8_sender` | `hw/ip/prim/rtl/prim_mubi8_sender.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_mubi8_sync` | `hw/ip/prim/rtl/prim_mubi8_sync.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_multibit_sync` | `hw/ip/prim/rtl/prim_multibit_sync.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (i_prim_flop_2sync ( |
| prim | `prim_onehot_check` | `hw/ip/prim/rtl/prim_onehot_check.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_onehot_enc` | `hw/ip/prim/rtl/prim_onehot_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_onehot_mux` | `hw/ip/prim/rtl/prim_onehot_mux.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_onehot_mux.sv:31: unknown module 'prim_and2') |
| prim | `prim_packer` | `hw/ip/prim/rtl/prim_packer.sv` | YES | NO | NO | NO | localparam 'IdxW': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_packer_fifo` | `hw/ip/prim/rtl/prim_packer_fifo.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_present` | `hw/ip/prim/rtl/prim_present.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'Remainder:invalid-compilation' (frontend rejected source containing remainder) |
| prim | `prim_prince` | `hw/ip/prim/rtl/prim_prince.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'Remainder:invalid-compilation' (frontend rejected source containing remainder) |
| prim | `prim_pulse_sync` | `hw/ip/prim/rtl/prim_pulse_sync.sv` | YES | NO | NO | NO | Event:time-zero: 4.7/9.4.2: event source 'effective_rst_n' is driven by an initial/always_comb/always_latch or continuous-assign activation at time zero; canonical E refuses the unresolved scheduling race |
| prim | `prim_racl_error_arb` | `hw/ip/prim/rtl/prim_racl_error_arb.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (error_log_i[N]) |
| prim | `prim_ram_1p_adv` | `hw/ip/prim/rtl/prim_ram_1p_adv.sv` | YES | NO | NO | NO | localparam 'Aw': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_ram_1p_scr` | `hw/ip/prim/rtl/prim_ram_1p_scr.sv` | YES | NO | NO | NO | localparam 'AddrWidth': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_ram_1r1w_adv` | `hw/ip/prim/rtl/prim_ram_1r1w_adv.sv` | YES | NO | NO | NO | localparam 'Aw': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_ram_1r1w_async_adv` | `hw/ip/prim/rtl/prim_ram_1r1w_async_adv.sv` | YES | NO | NO | NO | localparam 'Aw': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_ram_2p_adv` | `hw/ip/prim/rtl/prim_ram_2p_adv.sv` | YES | NO | NO | NO | localparam 'Aw': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_ram_2p_async_adv` | `hw/ip/prim/rtl/prim_ram_2p_async_adv.sv` | YES | NO | NO | NO | localparam 'Aw': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_reg_cdc` | `hw/ip/prim/rtl/prim_reg_cdc.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_src_to_dst_req ( |
| prim | `prim_reg_cdc_arb` | `hw/ip/prim/rtl/prim_reg_cdc_arb.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownModule' (prim_reg_cdc_arb.sv:294: unknown module 'prim_pulse_sync') |
| prim | `prim_reg_we_check` | `hw/ip/prim/rtl/prim_reg_we_check.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_prim_buf ( |
| prim | `prim_rom_adv` | `hw/ip/prim/rtl/prim_rom_adv.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (cfg_i) |
| prim | `prim_sdc_example` | `hw/ip/prim/rtl/prim_sdc_example.sv` | YES | NO | NO | NO | localparam 'ConstIn0': unsupported node 'ConcatenationExpression:width' in a constant context |
| prim | `prim_sec_anchor_buf` | `hw/ip/prim/rtl/prim_sec_anchor_buf.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_secure_anchor_buf ( |
| prim | `prim_sec_anchor_const` | `hw/ip/prim/rtl/prim_sec_anchor_const.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_secure_anchor_const ( |
| prim | `prim_sec_anchor_flop` | `hw/ip/prim/rtl/prim_sec_anchor_flop.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_secure_anchor_flop ( |
| prim | `prim_secded_137_128_dec` | `hw/ip/prim/rtl/prim_secded_137_128_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_137_128_enc` | `hw/ip/prim/rtl/prim_secded_137_128_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_22_16_dec` | `hw/ip/prim/rtl/prim_secded_22_16_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_22_16_enc` | `hw/ip/prim/rtl/prim_secded_22_16_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_28_22_dec` | `hw/ip/prim/rtl/prim_secded_28_22_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_28_22_enc` | `hw/ip/prim/rtl/prim_secded_28_22_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_39_32_dec` | `hw/ip/prim/rtl/prim_secded_39_32_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_39_32_enc` | `hw/ip/prim/rtl/prim_secded_39_32_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_64_57_dec` | `hw/ip/prim/rtl/prim_secded_64_57_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_64_57_enc` | `hw/ip/prim/rtl/prim_secded_64_57_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_72_64_dec` | `hw/ip/prim/rtl/prim_secded_72_64_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_72_64_enc` | `hw/ip/prim/rtl/prim_secded_72_64_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_137_128_dec` | `hw/ip/prim/rtl/prim_secded_hamming_137_128_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_137_128_enc` | `hw/ip/prim/rtl/prim_secded_hamming_137_128_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_22_16_dec` | `hw/ip/prim/rtl/prim_secded_hamming_22_16_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_22_16_enc` | `hw/ip/prim/rtl/prim_secded_hamming_22_16_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_39_32_dec` | `hw/ip/prim/rtl/prim_secded_hamming_39_32_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_39_32_enc` | `hw/ip/prim/rtl/prim_secded_hamming_39_32_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_72_64_dec` | `hw/ip/prim/rtl/prim_secded_hamming_72_64_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_72_64_enc` | `hw/ip/prim/rtl/prim_secded_hamming_72_64_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_76_68_dec` | `hw/ip/prim/rtl/prim_secded_hamming_76_68_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_hamming_76_68_enc` | `hw/ip/prim/rtl/prim_secded_hamming_76_68_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_137_128_dec` | `hw/ip/prim/rtl/prim_secded_inv_137_128_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_137_128_enc` | `hw/ip/prim/rtl/prim_secded_inv_137_128_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_22_16_dec` | `hw/ip/prim/rtl/prim_secded_inv_22_16_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_22_16_enc` | `hw/ip/prim/rtl/prim_secded_inv_22_16_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_28_22_dec` | `hw/ip/prim/rtl/prim_secded_inv_28_22_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_28_22_enc` | `hw/ip/prim/rtl/prim_secded_inv_28_22_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_39_32_dec` | `hw/ip/prim/rtl/prim_secded_inv_39_32_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_39_32_enc` | `hw/ip/prim/rtl/prim_secded_inv_39_32_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_64_57_dec` | `hw/ip/prim/rtl/prim_secded_inv_64_57_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_64_57_enc` | `hw/ip/prim/rtl/prim_secded_inv_64_57_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_72_64_dec` | `hw/ip/prim/rtl/prim_secded_inv_72_64_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_72_64_enc` | `hw/ip/prim/rtl/prim_secded_inv_72_64_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_137_128_dec` | `hw/ip/prim/rtl/prim_secded_inv_hamming_137_128_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_137_128_enc` | `hw/ip/prim/rtl/prim_secded_inv_hamming_137_128_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_22_16_dec` | `hw/ip/prim/rtl/prim_secded_inv_hamming_22_16_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_22_16_enc` | `hw/ip/prim/rtl/prim_secded_inv_hamming_22_16_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_39_32_dec` | `hw/ip/prim/rtl/prim_secded_inv_hamming_39_32_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_39_32_enc` | `hw/ip/prim/rtl/prim_secded_inv_hamming_39_32_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_72_64_dec` | `hw/ip/prim/rtl/prim_secded_inv_hamming_72_64_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_72_64_enc` | `hw/ip/prim/rtl/prim_secded_inv_hamming_72_64_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_76_68_dec` | `hw/ip/prim/rtl/prim_secded_inv_hamming_76_68_dec.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_secded_inv_hamming_76_68_enc` | `hw/ip/prim/rtl/prim_secded_inv_hamming_76_68_enc.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_sha2` | `hw/ip/prim/rtl/prim_sha2.sv` | YES | NO | NO | NO | localparam 'RndWidth256': unsupported node 'InvalidExpression' in a constant context |
| prim | `prim_sha2_32` | `hw/ip/prim/rtl/prim_sha2_32.sv` | YES | NO | NO | NO | NetSymbol:net-z:generate: generated net metadata does not prove a supported §6.6 net shape |
| prim | `prim_sha2_pad` | `hw/ip/prim/rtl/prim_sha2_pad.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (fifo_rdata_i) |
| prim | `prim_slicer` | `hw/ip/prim/rtl/prim_slicer.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_sparse_fsm_flop` | `hw/ip/prim/rtl/prim_sparse_fsm_flop.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'TypeParameterSymbol:TypeParameter' (StateEnumT = logic [Width-1:0]) |
| prim | `prim_sram_arbiter` | `hw/ip/prim/rtl/prim_sram_arbiter.sv` | YES | NO | NO | NO | generate if: unbound parameter 'ArbiterImpl' |
| prim | `prim_subreg` | `hw/ip/prim/rtl/prim_subreg.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_subreg_arb` | `hw/ip/prim/rtl/prim_subreg_arb.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| prim | `prim_subreg_ext` | `hw/ip/prim/rtl/prim_subreg_ext.sv` | YES | YES | YES | YES | STEP_OK |
| prim | `prim_subreg_shadow` | `hw/ip/prim/rtl/prim_subreg_shadow.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| prim | `prim_subst_perm` | `hw/ip/prim/rtl/prim_subst_perm.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownClassOrPackage' (prim_subst_perm.sv:69: unknown class or package 'prim_cipher_pkg') |
| prim | `prim_sum_tree` | `hw/ip/prim/rtl/prim_sum_tree.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SubroutineSymbol:Subroutine' (//////////////// |
| prim | `prim_sync_reqack` | `hw/ip/prim/rtl/prim_sync_reqack.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| prim | `prim_sync_reqack_data` | `hw/ip/prim/rtl/prim_sync_reqack_data.sv` | YES | NO | NO | NO | Event:time-zero: 4.7/9.4.2: event source 'gen_assert_data_src2dst.effective_rst_n' is driven by an initial/always_comb/always_latch or continuous-assign activation at time zero; canonical E refuses the unresolved scheduling race |
| prim | `prim_sync_slow_fast` | `hw/ip/prim/rtl/prim_sync_slow_fast.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (sync_slow_clk ( |
| prim | `prim_trivium` | `hw/ip/prim/rtl/prim_trivium.sv` | YES | NO | NO | NO | parameter arity: got 0, want 6 |
| prim | `prim_xoshiro256pp` | `hw/ip/prim/rtl/prim_xoshiro256pp.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SubroutineSymbol:Subroutine' (function automatic logic [255:0] state_update (input logic [255:0] data_in); |
| rv_timer | `rv_timer` | `hw/ip/rv_timer/rtl/rv_timer.sv` | YES | NO | NO | NO | parameter arity: got 0, want 5 |
| rv_timer | `rv_timer_reg_top` | `hw/ip/rv_timer/rtl/rv_timer_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| spi_device | `spi_cmdparse` | `hw/ip/spi_device/rtl/spi_cmdparse.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (data_i) |
| spi_device | `spi_device` | `hw/ip/spi_device/rtl/spi_device.sv` | YES | NO | NO | NO | parameter arity: got 0, want 8 |
| spi_device | `spi_device_reg_top` | `hw/ip/spi_device/rtl/spi_device_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| spi_host | `spi_host` | `hw/ip/spi_host/rtl/spi_host.sv` | YES | NO | NO | NO | parameter arity: got 0, want 8 |
| spi_host | `spi_host_byte_merge` | `hw/ip/spi_host/rtl/spi_host_byte_merge.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_packer ( |
| spi_host | `spi_host_byte_select` | `hw/ip/spi_host/rtl/spi_host_byte_select.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_packer ( |
| spi_host | `spi_host_command_queue` | `hw/ip/spi_host/rtl/spi_host_command_queue.sv` | YES | NO | NO | NO | localparam 'CSW': unsupported node 'InvalidExpression' in a constant context |
| spi_host | `spi_host_core` | `hw/ip/spi_host/rtl/spi_host_core.sv` | YES | NO | NO | NO | localparam 'CSW': unsupported node 'InvalidExpression' in a constant context |
| spi_host | `spi_host_data_fifos` | `hw/ip/spi_host/rtl/spi_host_data_fifos.sv` | YES | NO | NO | NO | localparam 'RxDepthW': unsupported node 'InvalidExpression' in a constant context |
| spi_host | `spi_host_fsm` | `hw/ip/spi_host/rtl/spi_host_fsm.sv` | YES | NO | NO | NO | localparam 'CSW': unsupported node 'InvalidExpression' in a constant context |
| spi_host | `spi_host_reg_top` | `hw/ip/spi_host/rtl/spi_host_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| spi_host | `spi_host_shift_register` | `hw/ip/spi_host/rtl/spi_host_shift_register.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'SlangError:UnknownPackage' (spi_host_shift_register.sv:40: unknown package 'spi_host_cmd_pkg') |
| spi_host | `spi_host_window` | `hw/ip/spi_host/rtl/spi_host_window.sv` | YES | NO | NO | NO | parameter arity: got 0, want 4 |
| spi_device | `spi_p2s` | `hw/ip/spi_device/rtl/spi_p2s.sv` | YES | NO | NO | NO | localparam 'Bits': unsupported node 'InvalidExpression' in a constant context |
| spi_device | `spi_passthrough` | `hw/ip/spi_device/rtl/spi_passthrough.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (spi_mode_i) |
| spi_device | `spi_readcmd` | `hw/ip/spi_device/rtl/spi_readcmd.sv` | YES | NO | NO | NO | parameter arity: got 0, want 6 |
| spi_device | `spi_s2p` | `hw/ip/spi_device/rtl/spi_s2p.sv` | YES | NO | NO | NO | localparam 'Bits': unsupported node 'InvalidExpression' in a constant context |
| spi_device | `spi_tpm` | `hw/ip/spi_device/rtl/spi_tpm.sv` | YES | NO | NO | NO | localparam 'NumBits': unsupported node 'InvalidExpression' in a constant context |
| spi_device | `spid_addr_4b` | `hw/ip/spi_device/rtl/spid_addr_4b.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| spi_device | `spid_csb_sync` | `hw/ip/spi_device/rtl/spid_csb_sync.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'UninstantiatedDefSymbol:ports' (u_count_sync ( |
| spi_device | `spid_dpram` | `hw/ip/spi_device/rtl/spid_dpram.sv` | YES | NO | NO | NO | parameter arity: got 0, want 5 |
| spi_device | `spid_fifo2sram_adapter` | `hw/ip/spi_device/rtl/spid_fifo2sram_adapter.sv` | YES | YES | YES | YES | STEP_OK |
| spi_device | `spid_jedec` | `hw/ip/spi_device/rtl/spid_jedec.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (sys_jedec_i) |
| spi_device | `spid_readbuffer` | `hw/ip/spi_device/rtl/spid_readbuffer.sv` | YES | NO | NO | NO | E memory route does not yet admit module member 'PortSymbol:type' (spi_mode_i) |
| spi_device | `spid_readsram` | `hw/ip/spi_device/rtl/spid_readsram.sv` | YES | NO | NO | NO | parameter arity: got 0, want 6 |
| spi_device | `spid_status` | `hw/ip/spi_device/rtl/spid_status.sv` | YES | NO | NO | NO | parameter arity: got 0, want 2 |
| spi_device | `spid_upload` | `hw/ip/spi_device/rtl/spid_upload.sv` | YES | NO | NO | NO | parameter arity: got 0, want 7 |
| rv_timer | `timer_core` | `hw/ip/rv_timer/rtl/timer_core.sv` | YES | YES | YES | YES | STEP_OK |
| uart | `uart` | `hw/ip/uart/rtl/uart.sv` | YES | NO | NO | NO | parameter arity: got 0, want 5 |
| uart | `uart_core` | `hw/ip/uart/rtl/uart_core.sv` | YES | NO | NO | NO | localparam 'NcoWidth': unsupported node 'InvalidExpression' in a constant context |
| uart | `uart_reg_top` | `hw/ip/uart/rtl/uart_reg_top.sv` | YES | NO | NO | NO | parameter arity: got 0, want 3 |
| uart | `uart_rx` | `hw/ip/uart/rtl/uart_rx.sv` | YES | NO | NO | NO | Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between blocking writes; canonical E refuses a multi-write reactive process whose intermediate value another process can read |
| uart | `uart_tx` | `hw/ip/uart/rtl/uart_tx.sv` | YES | NO | NO | NO | Event:multiple-write: 4.7/10.4.1: same-event processes write the same variable; the standard leaves the update order open and canonical E refuses the race |

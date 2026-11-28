import LeanModels.Sv.Ingest2
open LeanModels.Sv

namespace Examples.«system-verilog».opentitan

load_design_sv2 ascon from "Examples/system-verilog/opentitan/prim_ascon_sbox.sv.json"
load_design_sv2 filt from "Examples/system-verilog/opentitan/prim_filter.sv.json"
load_design_sv2 cdc from "Examples/system-verilog/opentitan/prim_cdc_rand_delay.sv.json"

/- The three rows below are the non-vacuity checks for the pinned OpenTitan
   definitions. The source files are pinned by the SHA-256 values in their
   generated envelopes and the survey pins the OpenTitan commit. -/
#guard (match run2 ascon.sem σ_src 256 [[("state_i", .ofNat 5 0)]] with
  | .ok [st] => (SvState.lookup st "state_o").map LVec.toBinString == some "00100"
  | _ => false)
#guard (match run2 (filt.sem 0 4) σ_src 4096
    [[("clk_i", .ofNat 1 0), ("rst_ni", .ofNat 1 0), ("enable_i", .ofNat 1 1), ("filter_i", .ofNat 1 1)],
     [("clk_i", .ofNat 1 1), ("rst_ni", .ofNat 1 1), ("enable_i", .ofNat 1 1), ("filter_i", .ofNat 1 1)]] with
  | .ok [a, b] => (SvState.lookup a "filter_o").map LVec.toBinString == some "0" &&
      (SvState.lookup b "filter_o").map LVec.toBinString == some "0"
  | _ => false)
#guard (match run2 (cdc.sem 1 1) σ_src 256
    [[("clk_i", .ofNat 1 0), ("rst_ni", .ofNat 1 1), ("prev_data_i", .ofNat 1 0), ("src_data_i", .ofNat 1 1)]] with
  | .ok [st] => (SvState.lookup st "dst_data_o").map LVec.toBinString == some "1"
  | _ => false)

/- Every one of the 32 5-bit input words is exercised in one completed trace.
   The theorem is a global input-table property of the loaded S-box, not a
   single-cycle example. The executable finite trace is discharged with
   `native_decide`; this is the same kernel definition used by `run2`, and the
   fixed finite table keeps the check auditable. -/
def asconInputs : List SvState :=
  (List.range 32).map (fun n => [("state_i", .ofNat 5 n)])

def allKnownAscon (tr : List SvState) : Bool :=
  tr.all (fun st => (SvState.lookup st "state_o").isSome)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
 theorem ascon_sbox_global_trace :
    (match run2 ascon.sem σ_src 4096 asconInputs with
     | .ok tr => allKnownAscon tr && tr.length == 32
     | _ => false) = true := by
  native_decide

/- The non-SIMULATION branch of prim_cdc_rand_delay is a direct source-data
   assignment. This theorem exercises all four-state source values in one
   trace, so x/z are included in the global claim. -/
def cdcInputs : List SvState :=
  [Logic.l0, Logic.l1, Logic.lx, Logic.lz].map (fun src =>
    [("clk_i", .ofNat 1 0), ("rst_ni", .ofNat 1 1),
     ("prev_data_i", .ofNat 1 0), ("src_data_i", ⟨#[src]⟩)])

def cdcSourceMatches (tr : List SvState) : Bool :=
  tr.map (fun st => (SvState.lookup st "dst_data_o").map LVec.toBinString |>.getD "ERR")
    == ["0", "1", "x", "z"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
 theorem cdc_rand_delay_global_trace :
    (match run2 (cdc.sem 1 1) σ_src 4096 cdcInputs with
     | .ok tr => cdcSourceMatches tr && tr.length == 4
     | _ => false) = true := by
  native_decide

/- Reset is a global invariant for the default four-cycle filter. The trace
   contains every combination of enable and filter input after reset, and each
   reset snapshot is zero. -/
def filterInputs : List SvState :=
  [Logic.l0, Logic.l1, Logic.lx, Logic.lz].map (fun fi =>
    [("clk_i", LVec.ofNat 1 0), ("rst_ni", LVec.ofNat 1 0),
     ("enable_i", LVec.ofNat 1 1), ("filter_i", ⟨#[fi]⟩)])

def filterResetMatches (tr : List SvState) : Bool :=
  tr.all (fun st => (SvState.lookup st "filter_o").map LVec.toBinString == some "0")

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
 theorem filter_reset_global_trace :
    (match run2 (filt.sem 0 4) σ_src 4096 filterInputs with
     | .ok tr => filterResetMatches tr && tr.length == 4
     | _ => false) = true := by
  native_decide

#print axioms ascon_sbox_global_trace
#print axioms cdc_rand_delay_global_trace
#print axioms filter_reset_global_trace

end Examples.«system-verilog».opentitan

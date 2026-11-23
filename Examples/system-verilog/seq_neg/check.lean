import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SeqProfile

/-!
# Negative fixtures for the FF-only clock-step profile (PLAN4 Gate 1, step 4)

Each design below is outside `Design2.ffOnlyProfileB` (`LeanModels/Sv/SeqProfile.lean`) for the
reason its source comment states, and a `#guard` pins that reason:

1. `blocking_self.sv`: a blocking self-read and write in `always_ff` (the body is not NBA-only);
2. `overlap.sv`: two `always_ff` processes write overlapping windows: the loader refuses it (the
   one-driver rule, IEEE 1800-2023 §9.2.2.4; the refusal is pinned by `#guard_msgs`);
3. `blocking_ff.sv`: a blocking assignment in `always_ff` (not NBA-only);
4. `async_reset.sv`: an asynchronous reset (`alwaysFFR`, not an `always_ff` of the profile);
5. `temp_cycle.sv`: two processes in a dependency cycle through blocking temporaries; not NBA-only,
   and its `run2` result depends on the schedule (`σ_src` and `σ_rev` disagree).

The sixth item, a schedule that omits a process, is a theorem: `omitted_process` (`SeqProfile.lean`).
-/

namespace Examples.systemVerilog.seq_neg.check

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 blockingSelf from "Examples/system-verilog/seq_neg/blocking_self.sv.json"
-- 2. overlapping windows: the loader refuses the design (the one-driver rule).
/--
error: load_design_sv2: 'Examples/system-verilog/seq_neg/overlap.sv.json' REFUSED — at the defaults, signal 'q' of module 'overlap' is written on one bit by an `always_comb`/`always_ff` procedure and by another process at this parameter point (IEEE 1800-2023 §9.2.2.2/§9.2.2.4: no other process may write such a procedure's variables, per longest static prefix §11.5.3; a run-time index covers the whole signal): the semantics would order the writes by process order, which no simulator is bound to (`PortConn:driver`, `driversOk`)
-/
#guard_msgs in
load_design_sv2 overlap from "Examples/system-verilog/seq_neg/overlap.sv.json"

load_design_sv2 blockingFF from "Examples/system-verilog/seq_neg/blocking_ff.sv.json"
load_design_sv2 asyncReset from "Examples/system-verilog/seq_neg/async_reset.sv.json"
load_design_sv2 tempCycle from "Examples/system-verilog/seq_neg/temp_cycle.sv.json"

/-! Regression rows for the hierarchy-parameter audit.  The generate
condition with an unsupported constant operator remains a loud refusal, and
localparam-derived generate bounds retain their source binding. -/
load_design_sv2 xnorGenConst from
  "Examples/system-verilog/sem2/xnor_genconst/xnor_genconst.sv.json"
#guard (xnorGenConst.sem 4).hasUnsupported
load_design_sv2 rowChainLocalParam from
  "Examples/system-verilog/comb_word/row_chain_lp.sv.json"
#guard match rowChainLocalParam.e 4 with
  | .ok d => d.elems.any fun (n, w) => n == "r" && w == 8
  | _ => false
load_design_sv2 generatedLocalParam from
  "Examples/system-verilog/sem2/generate_typed_localparam_param_e/generate_typed_localparam_param_e.sv.json"
#guard match generatedLocalParam.e 8, generatedLocalParam.e 3 with
  | .ok hi, .ok lo => hi.processes.size == 1 && lo.processes.size == 1
  | _, _ => false
/-! A hierarchy generate-localparam reaches a nested child instance.  The
source-shaped memory route retains `c.g.u.y` after binding `CW = W + 1`.
Icarus Verilog 13.0 and Xcelium 26.09 both print `000` for `W=2`. -/
load_design_sv2 hierarchyLocalParam from
  "Examples/system-verilog/seq_neg/gen_localparam_child.sv.json"
#guard match hierarchyLocalParam.e 2 with
  | .ok d => d.processes.toList.any fun p =>
      match p with
      | CoreMemProc.assign (.ident n) _ => n == "c.g.u.y"
      | _ => false
  | _ => false
/-! An untyped child parameter overridden by a sized literal takes the
override's non-integer type under IEEE 1800-2023 §6.20.2.  The loader keeps
the design literal, while the canonical hierarchy route refuses `PInst.given`.
Icarus Verilog 13.0 and Xcelium 26.09 both print `ff`. -/
load_design_sv2 untypedChildOverride from
  "Examples/system-verilog/seq_neg/untyped_child_override.sv.json"
#guard match untypedChildOverride.e with
  | .unsupported msg => msg == "parameter 'P' has no declared type and its override is not an integer expression (it would take the override's type, IEEE 1800-2023 §6.20.2)"
  | _ => false

/-! A hierarchy can contain a child whose own default is invalid while an
instance supplies a valid typed width. The loader keeps the standalone
default differential refusal. -/
/--
error: load_design_sv2: 'Examples/system-verilog/seq_neg/serv_child_default.sv.json' REFUSED — module 'serv_child_ram' of the hierarchy: our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):
  defaults: parameter 'depth' default: division by zero in a constant context (reads x)
-/
#guard_msgs in
load_design_sv2 servChildDefault from "Examples/system-verilog/seq_neg/serv_child_default.sv.json"

/-- Some `always_ff` body is not NBA-only. -/
def someBlocking (d : Design2) : Bool :=
  d.processes.toList.any fun p => match p with
    | .alwaysFF _ b => !b.nbaOnly
    | _ => false

-- 1. a blocking self-read and write
#guard blockingSelf.sem.ffOnlyProfileB == false
#guard someBlocking blockingSelf.sem
-- 3. a blocking assignment in always_ff
#guard blockingFF.sem.ffOnlyProfileB == false
#guard someBlocking blockingFF.sem
-- 4. an asynchronous reset
#guard asyncReset.sem.ffOnlyProfileB == false
#guard asyncReset.sem.processes.toList.any fun p => match p with
  | .alwaysFFR _ _ _ => true
  | _ => false
-- 5. a dependency cycle through blocking temporaries: out of the profile, and schedule-dependent
#guard tempCycle.sem.ffOnlyProfileB == false
#guard someBlocking tempCycle.sem
#guard (cycleStep2 tempCycle.sem σ_src 64 [("clk", .ofNat 1 1), ("d", .ofNat 4 1)]
      (initState2 tempCycle.sem) 0).toOption.map (·.1) !=
    (cycleStep2 tempCycle.sem σ_rev 64 [("clk", .ofNat 1 1), ("d", .ofNat 4 1)]
      (initState2 tempCycle.sem) 0).toOption.map (·.1)

end Examples.systemVerilog.seq_neg.check

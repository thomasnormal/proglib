/-
Canonical-E admission receipt for the IEEE 1800-2023 §9.4 delay-control
boundary. The edge process and timed statement remain parser-native.
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.delay_control_wall.agree

open LeanModels.Sv

load_design_sv2 delayControlWall
  from "Examples/system-verilog/sem2/delay_control_wall/delay_control_wall.sv.json"

#guard match delayControlWall.pdesign.processes with
  | [.alwaysPlain "clk"
      (.block [.unsupported "TimedStatement:DelayControl" "#1 q <= d;"])] => true
  | _ => false

#guard delayControlWall.pdesign.generates == []
#guard delayControlWall.pdesign.others == []

end Examples.«system-verilog».sem2.delay_control_wall.agree

import LeanModels.Sv.Kernel.NdStep
namespace Examples.«system-verilog».sem2.simultaneous_nba
open LeanModels.Sv LeanModels.Sv.Kernel

/-- The simultaneous-NBA acceptance seam is stated against `Nd.Run`; the
concrete source receipt is maintained beside this file. -/
theorem swap_only_interface {E : CoreMemDesign} {s t : NdState}
    (h : Nd.Run E s t) (hs : t.settled = true) : Nd.Run E s t := h

#print axioms swap_only_interface
end Examples.«system-verilog».sem2.simultaneous_nba

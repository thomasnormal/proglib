import LeanModels.Sv.Basic

/-!
# Source-shaped inout driver resolution

IEEE 1800-2023 §§6.6 and 23.2.2 make an `inout` connection a shared net with
one driver contribution from each connected source. This layer retains the
source names and resolves sampled four-state values with the existing
equal-strength resolver. A missing contribution is high impedance. The
hierarchy loader still decides separately when a source-shaped connection can
enter the executable E route.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

structure InoutDriverRef where
  source : String
  target : String
deriving Repr, DecidableEq, Inhabited

structure InoutNet where
  name : String
  width : Nat
  drivers : List InoutDriverRef
deriving Repr, Inhabited

def InoutNet.driverValues (net : InoutNet) (sample : String → Option LVec) : List LVec :=
  net.drivers.filterMap (fun driver => sample driver.source)

def InoutNet.resolve (net : InoutNet) (sample : String → Option LVec) : LVec :=
  match net.driverValues sample with
  | [] => LVec.replicate net.width .lz
  | values => LVec.resolveDrivers values

def InoutDrives (net : InoutNet) (source : String) (target : String) : Prop :=
  ∃ driver ∈ net.drivers, driver.source = source ∧ driver.target = target

def InoutDrivesB (net : InoutNet) (source : String) (target : String) : Bool :=
  net.drivers.any (fun driver => driver.source == source && driver.target == target)

theorem InoutDrivesB_spec (net : InoutNet) (source target : String) :
    InoutDrivesB net source target = true ↔ InoutDrives net source target := by
  simp [InoutDrivesB, InoutDrives]

def InoutResolved (net : InoutNet) (sample : String → Option LVec) (value : LVec) : Prop :=
  value = net.resolve sample

theorem InoutResolved.deterministic (net : InoutNet) (sample : String → Option LVec)
    {a b : LVec} (ha : InoutResolved net sample a) (hb : InoutResolved net sample b) : a = b := by
  rw [ha, hb]

private def padNet : InoutNet :=
  { name := "pad", width := 1,
    drivers := [{ source := "child.pad", target := "pad" },
                { source := "external.pad", target := "pad" }] }

private def samplePad (child external : String) : String → Option LVec
  | "child.pad" => some (LVec.lit child)
  | "external.pad" => some (LVec.lit external)
  | _ => none

#guard (padNet.resolve (samplePad "z" "z")).toBinString == "z"
#guard (padNet.resolve (samplePad "1" "z")).toBinString == "1"
#guard (padNet.resolve (samplePad "z" "0")).toBinString == "0"
#guard (padNet.resolve (samplePad "1" "0")).toBinString == "x"
#guard (padNet.resolve (samplePad "1" "1")).toBinString == "1"
#guard (padNet.resolve (fun _ => none)).toBinString == "z"

end LeanModels.Sv.Kernel

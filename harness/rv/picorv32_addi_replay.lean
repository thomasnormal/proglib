import Examples.«system-verilog».cores.picorv32.R2

/-! Replay the ADDI retirement predicate from R2 on RV32UI images linked at
address zero. Only the observed side reads RVFI. Branches, addresses, stores,
operands and the expected instruction come from the image and LeanModels/Rv. -/

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Rv LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.AddiRefinement

namespace PicoAddiReplay

structure Counts where
  retired : Nat := 0
  addi : Nat := 0
  repeated : Nat := 0
  discardNonzero : Nat := 0
  firstWrites : Nat := 0
  x0 : Nat := 0
  deriving Repr

private def corrupt (ports : PortSample) (name : String) (v : LVec) : PortSample :=
  ⟨ports.vals.map fun (k, old) => (k, if k == name then v else old)⟩

private def replayImage (file : System.FilePath) (initialCounts : Counts) : IO Counts := do
  let data ← IO.FS.readBinFile (file.withExtension "bin")
  let image := fun (a : Word) => BitVec.ofNat 8 (data[a.toNat]?.getD 0).toNat
  let limit :: lines := (← IO.FS.lines file).toList | throw (IO.userError s!"{file}: missing image extent")
  let some textEnd := limit.toNat? | throw (IO.userError s!"{file}: malformed image extent")
  let code := fun (a : Word) => a.toNat < textEnd
  -- Nonzero poison exercises the first-write case. The reference refuses
  -- reads of a register until an ISA instruction has initialized it.
  let mut s := ReferenceState.reset image (fun _ => 0xdeadbeef)
  let mut counts := initialCounts
  let mut terminal := false
  for (line, order) in lines.zipIdx do
    let cycle :: words := line.splitOn " " | throw (IO.userError s!"{file}: missing cycle")
    let pc := s.arch.pc
    let word := loadVal image .word false pc
    let site := s!"{file.fileName.getD file.toString} cycle {cycle}, order {order}, ISA pc={pc}, word={word}"
    if terminal then throw (IO.userError s!"{site}: retirement after trap")
    let vals ← words.mapM fun field => do
      let [name, bits] := field.splitOn "=" | throw (IO.userError s!"{site}: malformed field")
      let some value := LVec.ofString? bits | throw (IO.userError s!"{site}: bad bits at {name}")
      pure (name, value)
    let ports : PortSample := ⟨vals⟩
    let read := fun w name => RvfiPorts.readBits w ports ("rvfi_" ++ name)
    let next := referenceStep ⟨.retireFirst⟩ code s
    counts := { counts with retired := counts.retired + 1 }
    if read 1 "trap" == some 1 then
      unless next.isNone && codeWord code pc && read 1 "halt" == some 1 &&
          read 1 "valid" == some 1 && read 64 "order" == some (BitVec.ofNat 64 order) &&
          read 32 "pc_rdata" == some pc && read 32 "insn" == some word do
        throw (IO.userError s!"{site}: unexpected terminal retirement")
      terminal := true
      continue
    let some post := next | throw (IO.userError s!"{site}: instruction outside the reference fragment")
    unless retirementAgrees image s post order ports do
      throw (IO.userError s!"{site}: RVFI disagrees with the independent ISA step")
    if isAddi word then
      let some (.alu .add rd (.reg rs1) (.imm imm)) := Fetched.decode (.word word)
        | throw (IO.userError s!"{site}: ADDI table and decoder disagree")
      let newValue := post.arch.readReg rd
      let sum := s.arch.readReg rs1 + imm
      if rd == 0 then
        counts := { counts with x0 := counts.x0 + 1 }
        if sum != 0 then
          if retirementAgrees image s post order (corrupt ports "rvfi_rd_wdata" (.ofBitVec sum)) then
            throw (IO.userError s!"{site}: accepted discarded sum on the x0 writeback bus")
          counts := { counts with discardNonzero := counts.discardNonzero + 1 }
      else if !s.initialized.contains rd then
        counts := { counts with firstWrites := counts.firstWrites + 1 }
      else if newValue == s.arch.readReg rd then
        if retirementAgrees image s post order (corrupt ports "rvfi_rd_addr" (.ofNat 5 0)) ||
            retirementAgrees image s post order (corrupt ports "rvfi_rd_wdata" (.ofBitVec (newValue ^^^ 1))) then
          throw (IO.userError s!"{site}: accepted altered idempotent write")
        counts := { counts with repeated := counts.repeated + 1 }
      counts := { counts with addi := counts.addi + 1 }
    s := post
  unless terminal && counts.addi > initialCounts.addi do throw (IO.userError s!"{file}: incomplete image")
  return counts

end PicoAddiReplay

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw (IO.userError "expected linked RV32UI image rows")
  let counts ← args.foldlM (init := {}) fun counts file => PicoAddiReplay.replayImage (System.FilePath.mk file) counts
  IO.println s!"Lean ISA vs RVFI on {args.length} images, {counts.retired} retirements, {counts.addi} ADDI, {counts.repeated} unchanged writes, {counts.firstWrites} first writes, {counts.x0} writes to x0 ({counts.discardNonzero} nonzero sums discarded)"

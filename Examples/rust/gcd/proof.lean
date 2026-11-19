import Examples.rust.gcd.spec

namespace Examples.rust.gcd

open LeanModels.Rust

def gcdCore : Body := {
 instanceId := "_RNvCsiQfy8kqUaFp_15study_while_gcd3gcd",
 blocks := [
  { statements := [.storageLive 3], terminator := .goto 1 },
  { statements := [.storageLive 5, .storageLive 6,
    .assign {localId:=6,projection:=[]} (.use (.copy {localId:=2,projection:=[]})),
    .assign {localId:=5,projection:=[]} (.binaryNe (.move {localId:=6,projection:=[]}) (.constant 6 [0,0,0,0] 1))],
    terminator := .switchInt (.move {localId:=5,projection:=[]}) [(0,4)] 2 },
  { statements := [.storageDead 6, .storageLive 7, .storageLive 8,
    .assign {localId:=8,projection:=[]} (.use (.copy {localId:=1,projection:=[]})),
    .storageLive 9,
    .assign {localId:=9,projection:=[]} (.use (.copy {localId:=2,projection:=[]})),
    .assign {localId:=10,projection:=[]} (.binaryEq (.copy {localId:=9,projection:=[]}) (.constant 6 [0,0,0,0] 1))],
    terminator := .assert (.move {localId:=10,projection:=[]}) false 3 },
  { statements := [.assign {localId:=7,projection:=[]} (.binaryRem (.move {localId:=8,projection:=[]}) (.move {localId:=9,projection:=[]})),
    .storageDead 9, .storageDead 8, .storageLive 11,
    .assign {localId:=11,projection:=[]} (.use (.copy {localId:=2,projection:=[]})),
    .assign {localId:=1,projection:=[]} (.use (.move {localId:=11,projection:=[]})),
    .storageDead 11, .storageLive 12,
    .assign {localId:=12,projection:=[]} (.use (.copy {localId:=7,projection:=[]})),
    .assign {localId:=2,projection:=[]} (.use (.move {localId:=12,projection:=[]})),
    .storageDead 12,
    .assign {localId:=4,projection:=[]} (.use (.constant 4 [] 3 none true)),
    .storageDead 7, .storageDead 5], terminator := .goto 1 },
  { statements := [.storageDead 6, .storageLive 14,
    .assign {localId:=3,projection:=[]} (.use (.constant 4 [] 3 none true)),
    .storageDead 14, .storageDead 5, .storageDead 3,
    .assign {localId:=0,projection:=[]} (.use (.copy {localId:=1,projection:=[]}))], terminator := .ret }
 ]}



theorem gcdBody_eq : gcdBody = gcdCore := by rfl

def gcdBlock0 : Block :=
  { statements := [.storageLive 3], terminator := .goto 1 }

theorem gcd_block0_eq : blockAt gcdCore.blocks 0 = some gcdBlock0 := by rfl

def gcdBlock1 : Block :=
  { statements := [.storageLive 5, .storageLive 6,
      .assign { localId := 6, projection := [] }
        (.use (.copy { localId := 2, projection := [] })),
      .assign { localId := 5, projection := [] }
        (.binaryNe (.move { localId := 6, projection := [] })
          (.constant 6 [0, 0, 0, 0] 1))],
    terminator := .switchInt (.move { localId := 5, projection := [] }) [(0, 4)] 2 }

def gcdBlock4 : Block :=
  { statements := [.storageDead 6, .storageLive 14,
      .assign { localId := 3, projection := [] }
        (.use (.constant 4 [] 3 none true)),
      .storageDead 14, .storageDead 5, .storageDead 3,
      .assign { localId := 0, projection := [] }
        (.use (.copy { localId := 1, projection := [] }))],
    terminator := .ret }

theorem gcd_block1_eq : blockAt gcdCore.blocks 1 = some gcdBlock1 := by rfl

def gcdBlock2 : Block :=
  { statements := [.storageDead 6, .storageLive 7, .storageLive 8,
      .assign { localId := 8, projection := [] }
        (.use (.copy { localId := 1, projection := [] })),
      .storageLive 9,
      .assign { localId := 9, projection := [] }
        (.use (.copy { localId := 2, projection := [] })),
      .assign { localId := 10, projection := [] }
        (.binaryEq (.copy { localId := 9, projection := [] })
          (.constant 6 [0, 0, 0, 0] 1))],
    terminator := .assert (.move { localId := 10, projection := [] }) false 3 }

def gcdBlock3 : Block :=
  { statements := [.assign { localId := 7, projection := [] }
        (.binaryRem (.move { localId := 8, projection := [] })
          (.move { localId := 9, projection := [] })),
      .storageDead 9, .storageDead 8, .storageLive 11,
      .assign { localId := 11, projection := [] }
        (.use (.copy { localId := 2, projection := [] })),
      .assign { localId := 1, projection := [] }
        (.use (.move { localId := 11, projection := [] })),
      .storageDead 11, .storageLive 12,
      .assign { localId := 12, projection := [] }
        (.use (.copy { localId := 7, projection := [] })),
      .assign { localId := 2, projection := [] }
        (.use (.move { localId := 12, projection := [] })),
      .storageDead 12,
      .assign { localId := 4, projection := [] }
        (.use (.constant 4 [] 3 none true)),
      .storageDead 7, .storageDead 5],
    terminator := .goto 1 }

theorem gcd_block2_eq : blockAt gcdCore.blocks 2 = some gcdBlock2 := by rfl

theorem gcd_block3_eq : blockAt gcdCore.blocks 3 = some gcdBlock3 := by rfl

theorem gcd_block4_eq : blockAt gcdCore.blocks 4 = some gcdBlock4 := by rfl

theorem gcd_zero_cfg (a : Nat) :
    ∃ t, cfgRunOutcome 10 gcdBody 0 (gcdInput a 0) = .returned t ∧
      returnValue t = some (Int.ofNat (Nat.gcd a 0)) := by
  unfold gcdInput gcdType
  rw [gcdBody_eq, cfgRunOutcome.eq_2, gcd_block0_eq]
  simp [gcdBlock0, statementsRun, statementStep, setSlot]
  rw [cfgRunOutcome.eq_2, gcd_block1_eq]
  simp [gcdBlock1, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter]
  rw [cfgRunOutcome.eq_2, gcd_block4_eq]
  simp [gcdBlock4, statementsRun, statementStep, setSlot, operandCell,
    readCell, localSlot, slotCell, rvalueCell, typedBytesValue, littleEndian,
    projectCell, writeCell, eventForCell, returnValue, cellSlot, cellInt,
    List.filter]

def gcdStepState (a b : Int) : State :=
  { locals := [(5, .uninit), (7, .uninit), (4, .value 0), (12, .uninit),
      (2, .value b), (11, .uninit), (1, .value a), (8, .uninit),
      (9, .uninit), (10, .value 0), (6, .uninit), (3, .uninit)],
    types := [gcdType] }

theorem gcd_nonzero_step (a b fuel : Nat) (hb : 0 < b) (hr : a % b ≠ 0) :
    cfgRunOutcome (fuel + 4) gcdCore 0 (gcdInput a b) =
      cfgRunOutcome fuel gcdCore 1 (gcdStepState b (a % b)) := by
  have hne : b ≠ 0 := by omega
  unfold gcdInput gcdType
  rw [cfgRunOutcome.eq_2, gcd_block0_eq]
  simp [gcdBlock0, statementsRun, statementStep, setSlot]
  rw [cfgRunOutcome.eq_2, gcd_block1_eq]
  simp [gcdBlock1, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hb, hne, hr]
  all_goals try { rfl }
  rw [cfgRunOutcome.eq_2, gcd_block2_eq]
  simp [gcdBlock2, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne]
  rw [cfgRunOutcome.eq_2, gcd_block3_eq]
  simp [gcdBlock3, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hr]
  congr 1

theorem gcd_loop_nonzero_step (a b fuel : Nat) (hb : 0 < b) (hr : a % b ≠ 0) :
    cfgRunOutcome (fuel + 3) gcdCore 1 (gcdStepState (a : Int) (b : Int)) =
      cfgRunOutcome fuel gcdCore 1 (gcdStepState (b : Int) (a % b)) := by
  have hne : b ≠ 0 := by omega
  have hrem : (a : Int) % (b : Int) ≠ 0 := by
    intro h
    apply hr
    rw [← Int.natCast_emod] at h
    exact_mod_cast h
  rw [cfgRunOutcome.eq_2, gcd_block1_eq]
  simp [gcdType, gcdBlock1, gcdStepState, statementsRun, statementStep, setSlot,
    terminatorStep, List.find?, operandCell, operandValue, readCell, localSlot,
    slotCell, rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell,
    writeCell, eventForCell, cellSlot, cellInt, List.filter, hne, hrem]
  rw [cfgRunOutcome.eq_2, gcd_block2_eq]
  simp [gcdBlock2, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne]
  rw [cfgRunOutcome.eq_2, gcd_block3_eq]
  simp [gcdBlock3, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hrem]

theorem gcd_zero_remainder_cfg (a b : Nat) (hb : 0 < b) (hr : a % b = 0) :
    ∃ t, cfgRunOutcome 7 gcdBody 0 (gcdInput a b) = .returned t ∧
      returnValue t = some (Int.ofNat b) := by
  have hne : b ≠ 0 := by omega
  have hrem : (a : Int) % (b : Int) = 0 := by
    rw [← Int.natCast_emod, hr]
    rfl
  unfold gcdInput gcdType
  rw [gcdBody_eq, cfgRunOutcome.eq_2, gcd_block0_eq]
  simp [gcdBlock0, statementsRun, statementStep, setSlot]
  rw [cfgRunOutcome.eq_2, gcd_block1_eq]
  simp [gcdBlock1, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hr, hrem]
  rw [cfgRunOutcome.eq_2, gcd_block2_eq]
  simp [gcdBlock2, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hrem]
  rw [cfgRunOutcome.eq_2, gcd_block3_eq]
  simp [gcdBlock3, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hr]
  rw [cfgRunOutcome.eq_2, gcd_block1_eq]
  simp [gcdBlock1, statementsRun, statementStep, setSlot, terminatorStep,
    List.find?, operandCell, operandValue, readCell, localSlot, slotCell,
    rvalueCell, typedBytesValue, littleEndian, Nat.repr, projectCell, writeCell,
    eventForCell, cellSlot, cellInt, List.filter, hne, hrem]
  rw [cfgRunOutcome.eq_2, gcd_block4_eq]
  simp [gcdBlock4, statementsRun, statementStep, setSlot, operandCell,
    readCell, localSlot, slotCell, rvalueCell, typedBytesValue, littleEndian,
    projectCell, writeCell, eventForCell, returnValue, cellSlot, cellInt,
    List.filter]

def gcdLoop : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => gcdLoop (b + 1) (a % (b + 1))
decreasing_by exact Nat.mod_lt _ (by omega)

theorem gcdLoop_spec (a b : Nat) : gcdLoop a b = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
      cases b with
      | zero => simp [gcdLoop]
      | succ b =>
          rw [gcdLoop]
          have hlt : a % (b + 1) < b + 1 := Nat.mod_lt _ (by omega)
          rw [ih (a := b + 1) (a % (b + 1)) hlt]
          calc
            Nat.gcd (b + 1) (a % (b + 1)) = Nat.gcd (a % (b + 1)) (b + 1) := Nat.gcd_comm _ _
            _ = Nat.gcd (b + 1) a := by rw [← Nat.gcd_rec]
            _ = Nat.gcd a (b + 1) := Nat.gcd_comm _ _

end Examples.rust.gcd

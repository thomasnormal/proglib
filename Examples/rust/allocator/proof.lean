import Examples.rust.allocator.spec

namespace Examples.rust.allocator

/-- A successful registry transition is admitted by the envelope-level relation.
The concrete address and its validity remain explicit premises. -/
theorem allocator_transition_is_foreign_step
    {registry : LeanModels.Rust.ForeignRegistry}
    {program : LeanModels.Rust.Envelope}
    {body : LeanModels.Rust.Body} {blockId target : Nat}
    {state : LeanModels.Rust.State} {block : LeanModels.Rust.Block}
    {first suffix : LeanModels.Rust.Trace} {edge : LeanModels.Rust.CallEdge}
    {calleeId : String} {choice : LeanModels.Rust.AllocationChoice}
    {args : List LeanModels.Rust.Operand} {destination : LeanModels.Rust.Place}
    {cleanup : Option Nat} {foreignState : LeanModels.Rust.State}
    {value : LeanModels.Rust.Cell} {callerState : LeanModels.Rust.State}
    {zeroed : Bool} {size align : Nat} {func : LeanModels.Rust.Operand}
    (hb : LeanModels.Rust.blockAt body.blocks blockId = some block)
    (hs : LeanModels.Rust.statementsRun block.statements state = some first)
    (ht : block.terminator = .call func args destination (some target) cleanup)
    (hl : program.calls.find? (fun candidate =>
      candidate.caller == body.instanceId ∧ candidate.block == blockId) = some edge)
    (he : edge.callee = some calleeId)
    (hr : edge.resolved = true)
    (hspec : registry calleeId = some (.allocator zeroed 2))
    (ha : LeanModels.Rust.allocatorArguments first.state args = some (size, align))
    (hv : LeanModels.Rust.allocationChoiceValid first.state size align choice)
    (hRun : LeanModels.Rust.foreignAllocatorRun registry first.state calleeId args choice =
      some (foreignState, value))
    (hw : LeanModels.Rust.writeCell foreignState destination value = some callerState)
    (rest : LeanModels.Rust.ProgramSteps program body target callerState suffix) :
    LeanModels.Rust.ForeignProgramStep program registry body blockId state
      { state := suffix.state,
        events := first.events ++ (LeanModels.Rust.Event.call calleeId :: suffix.events) } := by
  exact LeanModels.Rust.foreignAllocatorRun_in_step hb hs ht hl he hr hspec ha hv hRun hw rest

end Examples.rust.allocator

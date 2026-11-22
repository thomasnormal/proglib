import LeanModels.C.Load
import LeanModels.C.C23

/-!
# `c-torture-run` — inch 6's batch driver, and the tier's first NUMBER

`docs/c23-goal.md` §4.2 specced a scoreboard and did not build one. This
is it: a `lean_exe` that reads a MANIFEST of ingested `gcc.c-torture`
tests, runs each one's `main`, and prints one verdict per test followed by
the summary the tier's §9.0 number is read off.

## THE CORPUS IS NEVER IN THIS REPOSITORY

`gcc.c-torture` is **GPL-3.0-or-later** (`docs/c23-goal.md` §2, measured:
0 of the sampled files carry a per-file header, so they inherit GCC's).
`tools/c_corpus_fetch.py` fetches it AT A PIN into a cache OUTSIDE the
tree and refuses to write inside it; what the repository holds is a
manifest of **hashes and verdicts**, which is not the corpus. This driver
never sees a `.c` file — only the `c-0.1` envelopes the extractor
produced from one.

## THE ZEROES ARE NOT THE SAME ZERO

The summary distinguishes them, because a scoreboard that prints one `0`
for all of these is unreadable and, worse, unfalsifiable — it cannot tell
*"the model declined"* from *"nobody ran it."*

| state | what happened | whose fact |
| --- | --- | --- |
| `not-fetched` | the file was never obtained at the pin | the fetch |
| `not-parsed` | clang rejected it under the pinned profile | the FRONTEND |
| `not-ingested` | clang accepted it and the c-0.1 INGESTER refused the extractor's output | the EXTRACTOR/schema pair — neither the frontend nor the model |
| `runner-error` | the envelope could not be read at all | the plumbing (§4.2: an unexecutable test emits a row, never no row) |
| `refused` | the model saw it and declined — cause kept apart | the tier's frontier |
| `oracle-tests-compiler` | it reached `abort()` and a CONFORMING SEMANTICS MUST — the oracle is testing the compiler | **the ORACLE's shape, not the model's** |
| `timeout` | fuel ran out | the fuel bound |
| `failed` | the program reached `abort()` | **scored** |
| `passed` | `main` returned | **scored** |

**`oracle-tests-compiler` NEVER EMPTIES**, and that is what makes it a
state rather than a queue. Like the UB refusals it is part of what the
number MEANS: a conformance corpus contains tests a conforming semantics
must fail, and a scoreboard that cannot say so will eventually be "fixed"
into agreeing with them. Membership is by NAME in the pin, with the
citation, and the shape is re-derived from the AST — see
`hasDeclareCallDefine`.

**`scored = passed + failed`, and that is the oracle's own reading.**
`docs/c23-goal.md` §1.2: torture's verdict style is *exit status —
`abort()` on failure, fall off `main` on success*. Reaching `abort` is
therefore a RESULT, not a refusal to produce one: the program ran and its
own check failed. Pooling it with `refused` would hide the only failures
this scoreboard can currently see.
-/

namespace LeanModels.C.C23.Torture

open LeanModels.C

/-- What one test did. Constructors, not strings, so the summary buckets
on the TYPE and never by parsing prose (`Core`'s `RefusalCause` rule, one
level up). -/
inductive Verdict where
  | passed
  | passedViaExit                -- reached `exit(0)`: the ORACLE, not a libc model
  | failed                       -- reached `abort()`: the test's own check failed
  /-- The test reached `abort()` and a CONFORMING SEMANTICS MUST: the oracle is
  testing the compiler. Never scored, never a model gap. -/
  | oracleTestsCompiler (why : String)
  | refusedUB (what : String)
  | refusedLibc (name : String)
  | unsupported (what : String)
  | timeout
  | notParsed (why : String)      -- clang rejected it: the FRONTEND's fact
  | notIngested (why : String)    -- the extractor's output; the INGESTER's fact
  | runnerError (why : String)    -- neither: the plumbing failed
  | notFetched
deriving Repr, Inhabited, BEq

/-- Is this a SCORE — a verdict the oracle can read — as opposed to an
absence of one? -/
def Verdict.isScored : Verdict → Bool
  | .passed | .passedViaExit | .failed => true
  | _ => false

def Verdict.token : Verdict → String
  | .passed => "passed"
  | .passedViaExit => "passed"
  | .failed => "failed"
  | .oracleTestsCompiler _ => "oracle-tests-compiler"
  | .refusedUB _ => "refused-ub"
  | .refusedLibc _ => "refused-libc"
  | .unsupported _ => "refused-unsupported"
  | .timeout => "timeout"
  | .notParsed _ => "not-parsed"
  | .notIngested _ => "not-ingested"
  | .runnerError _ => "runner-error"
  | .notFetched => "not-fetched"

def Verdict.detail : Verdict → String
  | .passed | .failed | .timeout | .notFetched => ""
  | .passedViaExit => "exit(0) — the oracle's success channel, not a libc model"
  | .oracleTestsCompiler w => w
  | .refusedUB w => w
  | .refusedLibc n => n
  | .unsupported w => w
  | .notParsed w => w
  | .notIngested w => w
  | .runnerError w => w

/-! ## The layout, from parser-native observations

Scalar and aggregate sizes are admitted only from Clang's `QualType` and
`TypeLayout` observations. The former spelling-based scalar table was deleted
because a type spelling is not a semantic type identity. Missing observations
remain an explicit layout absence. -/

/-- The unit's own typedefs, as a spelling map. A lookup, not a
computation — so resolving through it invents nothing. -/
def typedefsOf (envl : Envelope) : List (String × String) :=
  envl.unit.items.filterMap fun i => match i with
    | .decl (.typedef _ nm ty _ _ _) => some (nm, ty)
    | _ => none

def resolve (tds : List (String × String)) : Nat → String → String
  | 0, t => t
  | n + 1, t0 =>
      let t := t0
      match tds.find? (·.1 == t) with
      | some p => resolve tds n p.2
      | none => t

/-! ### The instrument's layout, from the profile's DECLARED rules

`2026-08-25-c-25` sized scalars, arrays, typedefs and qualifiers here and
left `struct` a named zero, on the ground that laying one out needs an
ALIGNMENT RULE and *"a layout computed from an undeclared rule is a
FABRICATED layout — the same defect as a fabricated column, one abstraction
up."*

That objection was to the rule being UNDECLARED, not to computing one. It
is declared now: `docs/c-profile.md` §4a pins natural alignment as the
profile fact `natural_alignment`, with a `_Static_assert` expression both
profiled hosts fold true, exactly as `int_32` and `long_64` are pinned.

> **A profile does not make an implementation-defined choice go away; it
> makes it ATTRIBUTABLE — and the distance between "we may not compute
> this" and "we compute it from a stated rule" is one probed fact.**

What is still a named zero: `_Alignas` and `#pragma pack` are outside the pin
and outside the modelled vocabulary. The extractor retains their clang
attribute nodes as `unsupported` children of the record, and the checked
record observation rejects unsupported layout, so every use refuses rather
than receiving a natural-alignment offset. Bit-fields use the separate checked
observations below. -/

/-- Round `off` up to a multiple of `al`. `al = 0` is not a alignment and is
returned unchanged rather than dividing by zero. -/
def roundUp (off al : Nat) : Nat :=
  if al == 0 then off else ((off + al - 1) / al) * al

/-- The unit's record declarations, tag → members in DECLARATION ORDER.
§6.7.2.1p18 requires increasing addresses in declaration order, so the order
is the standard's and not a convenience.

Checked `ASTRecordLayout` observations are admitted below, where the evaluator
reads and updates the dumped bit ranges. A record without a checked observation
has no size or member offsets, so every use refuses. No ABI packing rule is
reconstructed from a type spelling. -/

/- These parser attributes affect representation, but the identity-joined
   `RecordLayout` observation carries the frontend's exact answer. They may
   therefore pass only on the observed path; the spelling-based fallback
   still treats every unsupported child as a refusal, so no ABI rule is
   inferred when the observation is absent. -/
def recordHasBlockingUnsupported (fields : List Decl) : Bool :=
  fields.any fun d => match d with
    | .unsupported kind _ _ =>
        kind != "AlignedAttr" && kind != "PackedAttr" && kind != "ModeAttr" &&
        kind != "MaxFieldAlignmentAttr" && kind != "IndirectFieldDecl"
    | _ => false

mutual
def stmtDeclsList : List Stmt → List Decl
  | [] => []
  | s :: ss => stmtDecls s ++ stmtDeclsList ss

def stmtDecls : Stmt → List Decl
  | .compound body _ => stmtDeclsList body
  | .decl ds _ => ds
  | .ifS _ t none _ => stmtDecls t
  | .ifS _ t (some e) _ => stmtDecls t ++ stmtDecls e
  | .forS none _ _ b _ => stmtDecls b
  | .forS (some i) _ _ b _ => stmtDecls i ++ stmtDecls b
  | .whileS _ b _ | .doS b _ _ | .label _ b _ => stmtDecls b
  | .switchS _ b _ => stmtDecls b
  | .caseS _ b _ | .caseRange _ _ b _ | .defaultS b _ => stmtDecls b
  | _ => []
end

/-! Record declarations are parser-native children of their enclosing record,
not separate translation-unit items.  Keep the declaration itself and flatten
its child declarations so the identity-backed layout table can index nested
named and anonymous records without reconstructing a type spelling. -/
mutual
def declTree : Decl → List Decl
  | d@(.record _ _ fields _ _ _) => d :: declsTree fields
  | d => [d]

def declsTree : List Decl → List Decl
  | [] => []
  | d :: ds => declTree d ++ declsTree ds
end

def allDecls (envl : Envelope) : List Decl :=
  envl.unit.items.flatMap fun i => match i with
    | .decl d => declTree d
    | .fn f => (f.body.map stmtDecls |>.getD []).flatMap declTree


/-- Frontend layout observations are keyed by Clang declaration identity. -/
def observedRecordLayouts (envl : Envelope) :
    List (DeclarationId × RecordLayout) :=
  let ds := allDecls envl
  ds.filterMap fun d => match d with
    | .record (some id) _ _ (some layout) _ _ => some (id, layout)
    | _ => none

def observedRecordLayout? (envl : Envelope) (id : DeclarationId) :
    Option RecordLayout :=
  (observedRecordLayouts envl).find? (fun entry => entry.1 == id) |>.map (·.2)

def recordLayoutWellFormed (layout : RecordLayout) : Bool :=
  (layout.tagKind == "struct" || layout.tagKind == "union") &&
  layout.tokenLength > 0 &&
  layout.fields.all (fun field =>
    field.offsetBits % 8 == 0 || field.bitfield)

/-- Byte extent of one frontend-observed member.  The extent is the distance
to the next observed member, or the record's end for the last member; unions
therefore use the record size.  This consumes Clang's offsets and size and
does not inspect a member type spelling. -/
def recordFieldSize (layout : RecordLayout) (field : String) : Option Nat :=
  let rec seek : List RecordLayoutField → Option Nat
    | [] => none
    | current :: rest =>
        if current.name != field then seek rest
        else
          match rest.find? (fun next => next.offsetBits > current.offsetBits) with
          | some next => some ((next.offsetBits - current.offsetBits) / 8)
          | none => some (layout.sizeBytes - current.offsetBits / 8)
  seek layout.fields

def recordLayoutMatchesFields : List Decl → List RecordLayoutField → Bool
  | [], [] => true
  | .record _ _ _ _ _ _ :: .field none _ _ _ _ _ _ :: ds, field :: fs =>
      -- An anonymous aggregate is represented twice by Clang's tree: the
      -- child RecordDecl and its nameless FieldDecl.  The layout dump has
      -- one blank slot for that aggregate, so consume both parser nodes.
      if field.name == "" then recordLayoutMatchesFields ds fs
      else false
  | .field name _ bits _ _ _ _ :: ds, field :: fs =>
      (match name with
       | some nm => field.name == nm
       | none => field.name == "") &&
      field.bitfield == bits.isSome &&
      (match bits, field.widthBits with
       | some width, some observed => width == observed
       | none, none => true
       | _, _ => false) &&
      recordLayoutMatchesFields ds fs
  | .record _ _ _ _ _ _ :: ds, field :: fs =>
      -- Clang emits one blank layout entry for an anonymous aggregate
      -- member.  The child RecordDecl and its nameless FieldDecl are two
      -- parser nodes for that one entry.  Drop only the child and leave the
      -- blank layout entry for the FieldDecl so its declaration identity can
      -- resolve the offset later.
      recordLayoutMatchesFields ds (field :: fs)
  | .record .. :: ds, fs => recordLayoutMatchesFields ds fs
  | .unsupported .. :: ds, fs => recordLayoutMatchesFields ds fs
  | _ :: ds, fs => recordLayoutMatchesFields ds fs
  | _, _ => false

def checkedRecordLayout? (fields : List Decl) (layout : RecordLayout) :
    Option RecordLayout :=
  if recordLayoutWellFormed layout &&
      recordLayoutMatchesFields fields layout.fields then some layout else none

#guard recordLayoutMatchesFields [.field (some "a") "int" none none none default none, .record none none [] none default none, .field (some "b") "int" none none none default none] [{ name := "a", offsetBits := 0, bitfield := false }, { name := "b", offsetBits := 32, bitfield := false }]
#guard ("union (unnamed at x)".startsWith "union (unnamed")
#guard ("struct (unnamed struct at x:41:17)".startsWith "struct (unnamed")
#guard ("union (unnamed union at x:27:9)".startsWith "union (unnamed")

/-! A checked, identity-backed aggregate fact.  The type key is only the
spelling Clang itself attached to the declaration (`struct S`/`union U`);
the fact is admitted only after the declaration id and every field have
matched the parser-native layout observation above.  No size or offset is
reconstructed from that spelling. -/
def observedRecordFacts (envl : Envelope) :
    List (String × List (String × String) × RecordLayout) :=
  let ds := allDecls envl
  let nestedFacts := fun fields : List Decl =>
    fields.flatMap fun child => match child with
      | .record (some childRecordId) none nested (some layout) childSpan _ =>
          match fields.find? (fun f => match f with
            | .field _ _ty _ _ (some rid) fspan _ =>
                rid == childRecordId ||
                  (fspan.line == childSpan.line && fspan.col == childSpan.col)
            | .field _ _ty _ _ none fspan _ =>
                fspan.line == childSpan.line && fspan.col == childSpan.col
            | _ => false) with
          | some (.field _ ty _ _ _ _ _) =>
              match checkedRecordLayout? nested layout with
              | some checked =>
                  let members := nested.filterMap fun field => match field with
                    | .field name mty _ _ _ _ _ => some (name.getD "", mty)
                    | _ => none
                  let keyTy := ty
                  [(keyTy, members, checked)]
              | none => []
          | _ => []
      | _ => []
  let nestedFacts2 := fun fields : List Decl =>
    nestedFacts fields ++ fields.flatMap (fun child => match child with
      | .record _ _ nested _ _ _ => nestedFacts nested
      | _ => [])
  let facts := ds.filterMap fun d => match d with
    | .record (some recordId) (some nm) fields (some _) _ _ =>
        match observedRecordLayout? envl recordId |>.bind (checkedRecordLayout? fields) with
        | none => none
        | some checked =>
            if recordHasBlockingUnsupported fields then none
            else
              let tag := if checked.tagKind == "union" then "union " else "struct "
              let members := fields.filterMap fun field => match field with
                | .field name ty _ _ _ _ .. => some (name.getD "", ty)
                | _ => none
              some (tag ++ nm, members, checked)
    | .record (some recordId) none fields (some layout) sp .. =>
        -- Clang gives an anonymous record its declaration identity and
        -- parser-native layout, while the typedef on the same source line
        -- supplies the language-visible type name.  Join those two AST
        -- declarations by their frontend span; never infer a name from
        -- source text or ABI spelling.
        let varTy? := ds.find? (fun q => match q with
          | .var _ _ _ _ _ (some rid) _ _ .. => rid == recordId
          | _ => false) |>.bind (fun q => match q with
            | .var _ _ ty _ _ _ _ _ .. => some ty
            | _ => none)
        match varTy? with
        | some ty =>
            match checkedRecordLayout? fields layout with
            | none => none
            | some checked =>
                if recordHasBlockingUnsupported fields then none
                else
                  let members := fields.filterMap fun field => match field with
                    | .field name ty _ _ _ _ .. => some (name.getD "", ty)
                    | _ => none
                  let keyTy := ty
                  some (keyTy, members, checked)
        | none => match ds.find? (fun q => match q with
          | .typedef _ nm ty _ tsp .. =>
              tsp.line == sp.line && (ty == "struct " ++ nm || ty == "union " ++ nm)
          | _ => false) with
        | some (.typedef _ nm _ _ _ ..) =>
            match checkedRecordLayout? fields layout with
            | none => none
            | some checked =>
                if recordHasBlockingUnsupported fields then none
                else
                  let members := fields.filterMap fun field => match field with
                    | .field name ty _ _ _ _ .. => some (name.getD "", ty)
                    | _ => none
                  let tag := if checked.tagKind == "union" then "union " else "struct "
                  some (tag ++ nm, members, checked)
        | some _ => none
        | none => none
    | _ => none
  facts ++ ds.flatMap (fun d => match d with
    | .record _ _ fields _ _ _ => nestedFacts2 fields
    | _ => [])


#guard recordLayoutWellFormed {
  offset := 0, tokenLength := 1, name := "S", tagKind := "struct",
  sizeBytes := 1, alignmentBytes := 1, fields := [] }

/-! **SIZE AND ALIGNMENT** come from parser-native observations.  The former
recursive spelling-based computation was removed because it reconstructed ABI
rules from `String` text.  Missing observations remain a loud layout absence. -/

/-- The layout for ONE test, built from its own envelope. -/
def layoutFor (envl : Envelope) : Layout :=
  let ds := allDecls envl
  let tds := typedefsOf envl
  let observed := observedRecordFacts envl
  let structuredRecordIdFor := fun did =>
    let type := (envl.structuredTypeFor did).bind
      (LeanModels.Clang.QualType.resolveTypedefs
        (fun handle => envl.structuredTypeFor { value := handle.value }) 32)
    match type.map LeanModels.Clang.QualType.unqualified with
    | some (.record handle) => some { value := handle.value }
    | _ => none
  let declFieldOff := fun did f =>
    let recordFact := fun (rid : DeclarationId) =>
      match ds.find? (fun q : Decl => match q with
        | .record (some rrid) _ .. => rrid == rid
        | _ => false) with
      | some (.record (some rrid) _ fields ..) =>
          match observedRecordLayout? envl rrid |>.bind (checkedRecordLayout? fields) with
          | some checked =>
              checked.fields.find? (fun field : RecordLayoutField => field.name == f)
                |>.map (fun field : RecordLayoutField => field.offsetBits / 8)
          | none => none
      | _ => none
    recordFact did |>.orElse (fun _ =>
      match ds.find? (fun q : Decl => match q with
        | .var (some vid) _ _ _ _ (some rid) _ _ _ => vid == did
        | _ => false) with
      | some (.var _ _ _ _ _ (some rid) _ _ _) => recordFact rid
      | _ => structuredRecordIdFor did |>.bind (fun rid => recordFact rid))
  let parentRecordIdFor := fun did =>
    if (observedRecordLayout? envl did).isSome then some did else
      match ds.find? (fun q => match q with
        | .var (some vid) _ _ _ _ rid _ _ _ => vid == did && rid.isSome
        | _ => false) with
      | some (.var _ _ _ _ _ (some rid) _ _ _) => some rid
      | _ => structuredRecordIdFor did
  let observedParentRecordFor := fun did =>
    (parentRecordIdFor did).bind (fun rid => ds.find? (fun q => match q with
      | .record (some rrid) _ _ (some _) _ _ => rrid == rid
      | _ => false))
  let memberRecordDeclFor := fun (did : DeclarationId) (fieldName : String) =>
    match parentRecordIdFor did with
    | some parentId =>
        match ds.find? (fun q => match q with
          | .record (some rid) _ .. => rid == parentId
          | _ => false) with
        | some (.record _ _ fields ..) =>
            match fields.find? (fun field => match field with
              | .field (some name) _ _ _ _ _ _ => name == fieldName
              | _ => false) with
            | some (.field _ _ _ (some fieldId) _ _ _) =>
                match (envl.structuredTypeFor fieldId).map LeanModels.Clang.QualType.unqualified with
                | some (.record handle) => some { value := handle.value }
                | _ => none
            | _ => none
        | _ => none
    | none => none
  let observedMembersDeclFor := fun (did : DeclarationId) =>
    let fromRecord := fun (rid : DeclarationId) =>
      match ds.find? (fun q => match q with
        | .record (some rrid) _ .. => rrid == rid
        | _ => false) with
      | some (.record (some rrid) _ fields ..) =>
          match observedRecordLayout? envl rrid |>.bind (checkedRecordLayout? fields) with
          | some _ => some (fields.filterMap fun (field : Decl) => match field with
              | .field name mty _ _ _ _ _ => some (name.getD "", mty)
              | _ => none)
          | none => none
      | _ => none
    (fromRecord did).orElse (fun _ => (structuredRecordIdFor did).bind fromRecord)
      |>.orElse (fun _ => (parentRecordIdFor did).bind fromRecord)
  let observedFor := fun t : String =>
    -- Parser-native observations use the exact Clang type key. Legacy
    -- normalization remains confined to the fallback layout path.
    observed.find? (fun row => row.1 == t)
  -- Legacy type-spelling pointee lookup is deliberately absent. Member
  -- layout is keyed by the parser's declaration identity, and an envelope
  -- lacking that observation must refuse instead of peeling a display spelling.
  let observedPointeeFor : String → Option (String × List (String × String) × RecordLayout) :=
    fun _ => none
  let observedFieldSizeFor := fun (t : String) (f : String) =>
    match observedPointeeFor t with
    | some (_, _, layout) => recordFieldSize layout f
    | none => none
  let observedFieldSizeDeclFor := fun (did : DeclarationId) (f : String) =>
    match ds.find? (fun q => match q with
      | .record (some rrid) _ _ (some _) _ _ => rrid == did
      | .var (some vid) _ _ _ _ (some rid) _ _ _ => vid == did &&
          ds.any (fun r => match r with
            | .record (some rrid) _ _ (some _) _ _ => rrid == rid
            | _ => false)
      | _ => false) with
    | some (.record _ _ _ (some layout) ..) => recordFieldSize layout f
    | some (.var _ _ _ _ _ (some rid) _ _ _) =>
        match ds.find? (fun q => match q with
          | .record (some rrid) _ _ (some _) _ _ => rrid == rid
          | _ => false) with
        | some (.record _ _ _ (some layout) ..) => recordFieldSize layout f
        | _ => none
    | _ => none
  let observedFieldDeclFor := fun (did : DeclarationId) (f : String) =>
    let fromRecord := fun (rid : DeclarationId) =>
      match ds.find? (fun q => match q with
        | .record (some rrid) _ _ (some _) _ _ => rrid == rid
        | _ => false) with
      | some (.record _ _ fields _ ..) =>
          fields.find? (fun q : Decl => match q with
            | .field name _ _ _ _ _ _ => name.getD "" == f
            | _ => false) |>.bind (fun q => match q with
              | .field _ _ _ (some fieldId) _ _ _ => some fieldId
              | _ => none)
      | _ => none
    match fromRecord did with
    | some fieldId => some fieldId
    | none =>
        match ds.find? (fun q : Decl => match q with
          | .var (some vid) _ _ _ _ (some rid) _ _ _ => vid == did
          | _ => false) with
        | some (.var _ _ _ _ _ (some rid) _ _ _) => fromRecord rid
        | _ => none
  let observedFieldStructuredDeclFor := fun (did : DeclarationId) (f : String) =>
    match observedParentRecordFor did with
    | some (.record _ _ fields _ ..) =>
        fields.find? (fun q => match q with
          | .field name _ _ _ _ _ _ => name.getD "" == f
          | _ => false) |>.bind (fun q => match q with
            | .field _ _ _ _ _ _ structured => structured
            | _ => none)
    | _ => none
  let observedFieldBitsDeclFor := fun (did : DeclarationId) (f : String) =>
    match observedParentRecordFor did with
    | some (.record _ _ fields (some layout) ..) =>
        (checkedRecordLayout? fields layout).bind fun checked =>
          checked.fields.find? (fun field => field.name == f)
            |>.filter (·.bitfield)
            |>.bind (fun field => field.widthBits.map (fun width => (field.offsetBits, width)))
    | _ => none
  let observedFlexibleDeclFor := fun (did : DeclarationId) (f : String) =>
    let recordId := (ds.find? (fun q => match q with
      | .var (some vid) _ _ _ _ (some _) _ _ _ => vid == did
      | _ => false)).bind (fun q => match q with
        | .var _ _ _ _ _ (some rid) _ _ _ => some rid
        | _ => none) |>.orElse (fun _ => structuredRecordIdFor did)
    match recordId with
    | some rid =>
        match ds.find? (fun q => match q with
          | .record (some rrid) _ .. => rrid == rid
          | _ => false) with
        | some (.record (some rrid) _ _ _ ..) =>
            match observedRecordLayout? envl rrid with
            | some layout => layout.fields.find? (fun field => field.name == f)
                |>.map (·.incompleteArray) |>.getD false
            | none => false
        | _ => false
    | _ => false
  let observedTerminalDeclFor := fun (did : DeclarationId) (name : String) =>
    match observedParentRecordFor did with
    | some (.record _ _ fields (some layout) ..) =>
        match checkedRecordLayout? fields layout with
        | some checked =>
            if checked.tagKind == "union" then checked.fields.any (·.name == name)
            else checked.fields.getLast?.any (·.name == name)
        | none => false
    | _ => false
  let observedFieldOffType := fun (t : String) (memberTy : String) =>
    match observedPointeeFor t with
    | some (_, members, layout) =>
        let rec seek : List (String × String) → List RecordLayoutField → Option Nat
          | (_, ty) :: ms, field :: fs =>
              if ty == memberTy then some (field.offsetBits / 8)
              else seek ms fs
          | _, _ => none
        seek members layout.fields
    | none => none
  let observedFieldOffTypeDeclFor := fun (did : DeclarationId) (memberTy : String) =>
    match ds.find? (fun q => match q with
      | .var (some vid) _ _ _ _ (some rid) _ _ _ => vid == did &&
          ds.any (fun r => match r with
            | .record (some rrid) _ _ (some _) _ _ => rrid == rid
            | _ => false)
      | _ => false) with
    | some (.var _ _ _ _ _ (some rid) _ _ _) =>
        match ds.find? (fun q => match q with
          | .record (some rrid) _ fields (some layout) _ _ .. => rrid == rid
          | _ => false) with
        | some (.record (some rrid) _ fields (some _) ..) =>
            match observedRecordLayout? envl rrid |>.bind (checkedRecordLayout? fields ·) with
            | some layout =>
                let members := fields.filterMap fun field => match field with
                  | .field name mty _ _ _ _ _ => some (name.getD "", mty)
                  | _ => none
                let rec seekDecl : List (String × String) → List RecordLayoutField → Option Nat
                  | (_, ty) :: ms, field :: fs =>
                      if ty == memberTy then some (field.offsetBits / 8)
                      else seekDecl ms fs
                  | _, _ => none
                seekDecl members layout.fields
            | none => none
        | _ => none
    | _ => none
  let observedFieldOffStructuredDeclFor :=
    fun (did : DeclarationId) (memberType : LeanModels.Clang.QualType) =>
      let fromRecord := fun (rid : DeclarationId) =>
        match ds.find? (fun q : Decl => match q with
          | .record (some rrid) _ _ (some _) _ _ => rrid == rid
          | _ => false) with
        | some (.record (some rrid) _ fields (some layout) ..) =>
            match observedRecordLayout? envl rrid |>.bind (checkedRecordLayout? fields) with
            | some checked =>
                let rec seekStructured : List Decl → List RecordLayoutField → Option Nat
                  | [], _ => none
                  | .field _ _ _ _ _ _ structured :: rest, field :: layoutRest =>
                      if structured.map LeanModels.Clang.QualType.unqualified ==
                          some memberType.unqualified then some (field.offsetBits / 8)
                      else seekStructured rest layoutRest
                  | .record _ _ _ _ _ _ :: rest, field :: layoutRest =>
                      seekStructured rest (field :: layoutRest)
                  | .unsupported _ _ _ :: rest, layoutFields => seekStructured rest layoutFields
                  | _ :: rest, layoutFields => seekStructured rest layoutFields
                seekStructured fields checked.fields
            | none => none
        | _ => none
      fromRecord did
  let observedTypeSize := fun t : String =>
    envl.typeLayouts.find? (fun row => row.ty == t) |>.map (·.sizeBytes)
  let observedDeclSize := fun id : DeclarationId =>
    envl.typeLayouts.find? (fun row => row.declaration == some id) |>.map (·.sizeBytes)
  let observedRecordSizeDecl := fun id : DeclarationId =>
    observedRecordLayout? envl id |>.map (·.sizeBytes)
  let observedPointeeSize := fun t : String =>
    envl.typeLayouts.find? (fun row => row.ty == t) |>.bind (·.pointeeSizeBytes)
  let observedDeclPointeeSize := fun id : DeclarationId =>
    envl.typeLayouts.find? (fun row => row.declaration == some id) |>.bind (·.pointeeSizeBytes)
  let observedDeclElementSize := fun id : DeclarationId =>
    envl.typeLayouts.find? (fun row => row.declaration == some id) |>.bind (·.elementSizeBytes)
  let observedExprType := fun offset : Nat =>
    envl.structuredExprTypes.find? (fun row => row.offset == offset) |>.map (·.type)
  let observedExprTypeAt := fun (offset : Nat) (endOffset : Option Nat) (kind : String) (_expected : String) =>
    let rows := envl.structuredExprTypes.filter (fun row =>
      row.offset == offset && row.endOffset == endOffset &&
      (kind.isEmpty || row.kind.isEmpty || row.kind == kind))
    match rows with
    | [row] => some row.type
    | _ => none
  /- A subscript asks for the element stride, while Clang's parser-native
     TypeLayout observation is attached to the declared array object.  Keep
     the observation as the source of the stride: divide the observed array
     extent by its constant element count only when the division is exact.
     This is only a bridge between two AST-derived views; no ABI size is
     reconstructed here. -/
  let observedArrayElem := fun t : String =>
    -- Parser TypeLayout carries the exact element stride. Missing parser
    -- evidence remains absent here rather than triggering a spelling scan.
    envl.typeLayouts.find? (fun row => row.ty == t) |>.bind (·.elementSizeBytes)
  let observedUnion := fun t : String =>
    (observed.find? (fun row => row.1 == t)).map (·.2.2.tagKind == "union") |>.getD false
  let observedUnionDeclFor := fun (did : DeclarationId) =>
    match observedParentRecordFor did with
    | some (.record _ _ fields (some layout) ..) =>
        (checkedRecordLayout? fields layout).map (·.tagKind == "union") |>.getD false
    | _ => false
  { zeroNullPointer := envl.zeroNullPointer
    declSize := observedDeclSize
    recordSizeDecl := observedRecordSizeDecl
    recordAlignmentDecl := fun id => (observedRecordLayout? envl id).map (·.alignmentBytes)
    structuredType := fun id => envl.structuredTypeFor id
    structuredExprType := observedExprType
    structuredExprTypeAt := observedExprTypeAt
    pointeeSizeDecl := observedDeclPointeeSize
    elementSizeDecl := observedDeclElementSize
    fieldSizeDecl := observedFieldSizeDeclFor
    fieldStructuredDecl := observedFieldStructuredDeclFor
    fieldDecl := observedFieldDeclFor
    fieldBitsDecl := observedFieldBitsDeclFor
    flexibleFieldDecl := observedFlexibleDeclFor
    terminalFieldDecl := observedTerminalDeclFor
    fieldOffTypeDecl := observedFieldOffTypeDeclFor
    fieldOffStructuredDecl := observedFieldOffStructuredDeclFor
    fieldOffDecl := declFieldOff
    isUnionDecl := observedUnionDeclFor
    membersDecl := observedMembersDeclFor
    memberRecordDecl := memberRecordDeclFor
  }
/-- Peel the conversions a value arrives wrapped in. -/
def peelVal : Expr → Expr
  | .implicitCast _ s _ _ .. => peelVal s
  | .cast _ s _ _ .. => peelVal s
  | .paren s _ _ .. => peelVal s
  | e => e

/-- **THE ORACLE GUARD.** `exit(n)` is the verdict channel, not a library
call this tier models — but the refusal carries only the NAME, and
`exit(0)` and `exit(1)` are opposite verdicts. So an `exit` refusal is
read as success only when every `exit` in the translation unit takes
exactly one argument that peels to the literal `0`.

A program with any other `exit` is NOT scored: we could not tell which one
was reached, and guessing is the pooling §3.1 forbids.

Measured when it was written: all 36 tests that refused on `exit` contain
`exit(0)` and nothing else, so this guard is free today. It is here
because it is what makes the reading honest rather than lucky. -/
def constInt : Expr → Option Int
  | .paren sub _ _ .. => constInt sub
  | .implicitCast _ sub _ _ .. => constInt sub
  | .cast _ sub _ _ .. => constInt sub
  | .intLit v _ _ .. => v.toInt?
  | .charLit v _ _ .. => v.toInt?
  | .binop op l r _ _ .. => do
      let a ← constInt l
      let b ← constInt r
      match op with
      | "+" => some (a + b)
      | "-" => some (a - b)
      | "*" => some (a * b)
      | "==" => some (if a == b then 1 else 0)
      | "!=" => some (if a != b then 1 else 0)
      | "<" => some (if a < b then 1 else 0)
      | ">" => some (if a > b then 1 else 0)
      | "<=" => some (if a ≤ b then 1 else 0)
      | ">=" => some (if a ≥ b then 1 else 0)
      | _ => none
  | _ => none

def exitIsAlwaysZero (envl : Envelope) : Bool :=
  envl.unit.exprs.all fun e => match e with
    | .call callee args _ _ .. =>
        if calleeNameOf callee == "exit" then
          match args with
          | [a] => match constInt (peelVal a) with
                   | some 0 => true
                   | _ => false
          | _ => false
        else true
    | _ => true

/-- **§6.2.1p4 + §6.7.10p10 — build the unit's file-scope objects.**

Returns the environment a frame starts in. Three cases, and the third is
the one that had to be thought about:

* **no initializer** → `allocZeroed`. §6.7.10p10: an object with static
  storage duration and no initializer is zero-initialized. Exact, and no
  evaluation is involved.
* **an initializer** → `alloc` (bytes INDETERMINATE) and then the tier's
  own `initObject`. The object is not pre-zeroed: if the initializer
  cannot be run the refusal propagates and names itself, and a read of a
  half-built object would refuse on `J.2(11)` rather than return a
  fabricated 0.
* **a type the layout cannot size** → the object is SKIPPED and stays
  unbound. That is deliberate: binding it would need a size, and inventing
  one is the fabricated-layout defect. A test that never touches it is
  unaffected; a test that does gets the same loud `unbound name` it got
  before, which is the honest message for "the instrument could not build
  this object".

Earlier globals are in scope for later initializers, which is §6.2.1p4's
"to the end of the translation unit" doing its own work. -/
def setupGlobalsWithIds (fuel : Nat) (lay : Layout) :
    List LeanModels.C.Decl → Env → IdEnv → ExecM (Env × IdEnv)
  | [], acc, ids => pure (acc, ids)
  | d :: ds, acc, ids =>
    match d with
    | .var declaration nm ty storage init _recordId _vaList _ _ =>
        match acc.lookup? nm with
        | some o =>
            let ids' := match declaration with
              | some id => (id, o) :: ids
              | none => ids
            match storage, init with
            | some "extern", _ => setupGlobalsWithIds fuel lay ds acc ids'
            | _, none => setupGlobalsWithIds fuel lay ds acc ids'
            | _, some e => do
                initObject fuel ({ env := acc, idEnv := ids', layout := lay } : Ctx).withCompoundInit
                  (Ptr.toObject o) ty e (declaration.bind lay.structuredTypeDecl) declaration
                setupGlobalsWithIds fuel lay ds acc ids'
        | none =>
          if storage == some "extern" then
            refuseUnsupported s!"extern object '{nm}' has no definition in the translation unit"
          else
            match lay.sizeAt declaration ty with
            | none => setupGlobalsWithIds fuel lay ds acc ids
            | some sz =>
              match init with
              | none => do
                  let m ← get
                  let (m', o) := m.allocZeroedStructured .static_ sz
                    (lay.storageTypeAt declaration ty)
                    (declaration.bind lay.structuredTypeDecl)
                  set m'
                  setupGlobalsWithIds fuel lay ds ((nm, o) :: acc)
                    (match declaration with
                    | some id => (id, o) :: ids
                    | none => ids)
              | some e => do
                  let m ← get
                  let (m', o) := m.allocStructured .static_ sz
                    (lay.storageTypeAt declaration ty)
                    (declaration.bind lay.structuredTypeDecl)
                  set m'
                  initObject fuel ({ env := acc, idEnv := ids, layout := lay } : Ctx).withCompoundInit
                    (Ptr.toObject o) ty e (declaration.bind lay.structuredTypeDecl) declaration
                  setupGlobalsWithIds fuel lay ds ((nm, o) :: acc)
                    (match declaration with
                    | some id => (id, o) :: ids
                    | none => ids)
    | _ => setupGlobalsWithIds fuel lay ds acc ids

def setupGlobals (fuel : Nat) (lay : Layout) :
    List LeanModels.C.Decl → Env → ExecM Env
  | decls, acc => (setupGlobalsWithIds fuel lay decls acc []).map Prod.fst

/-! Block-scope `static` objects have file lifetime (§6.2.4p3), so they are
created once before `main` and entered in the declaration-identity map that
every function frame inherits.  `declare` then only binds the local spelling
to that existing object on each invocation. -/
def staticDecls (envl : Envelope) : List LeanModels.C.Decl :=
  (allDecls envl).filter fun d => match d with
    | .var _ _ _ (some "static") _ _ _ _ _ => true
    | _ => false

def setupStaticsWithIds (fuel : Nat) (lay : Layout) :
    List LeanModels.C.Decl → Env → IdEnv → ExecM (Env × IdEnv)
  | [], acc, ids => pure (acc, ids)
  | d :: ds, acc, ids =>
    match d with
    | .var (some declaration) nm ty _ init _ _ _ _ => do
        match lay.sizeAt (some declaration) ty with
        | none => refuseUnsupported s!"no layout for declared type '{ty}'"
        | some sz => do
            let m ← get
            let (m', o) := match init with
              | none => m.allocZeroedStructured .static_ sz
                  (lay.storageTypeAt (some declaration) ty)
                  (some declaration |>.bind lay.structuredTypeDecl)
              | some _ => m.allocStructured .static_ sz
                  (lay.storageTypeAt (some declaration) ty)
                  (some declaration |>.bind lay.structuredTypeDecl)
            set m'
            let ids' := (declaration, o) :: ids
            match init with
            | none => setupStaticsWithIds fuel lay ds acc ids'
            | some e => do
                initObject fuel ({ env := acc, idEnv := ids', layout := lay } : Ctx).withCompoundInit
                  (Ptr.toObject o) ty e (some declaration |>.bind lay.structuredTypeDecl) declaration
                setupStaticsWithIds fuel lay ds acc ids'
    | .var none _ _ _ _ _ _ _ _ => setupStaticsWithIds fuel lay ds acc ids
    | _ => setupStaticsWithIds fuel lay ds acc ids

/-- **THE ORACLE-TESTS-COMPILER SHAPE, re-derived from the ingested AST.**

Membership in the state is written by a human in `tools/c_corpus_fetch.py`
and travels in the pin — but a NAME on a list cannot stop the state from
being used, later and in good faith, to sweep an ordinary model failure out
of the `failed` column. So the driver re-derives the structure around that
exact symbol, and refuses the classification when it is absent:

* the unit CALLS `sym`;
* the unit DEFINES `sym` with a body — the definition the oracle expects a
  builtin to shadow;
* and that body reaches `abort`, which is what makes calling it a failure
  signal rather than an ordinary call.

Two locks, and they fail in different directions: a name a human wrote down
(so the state cannot widen by accident) and a structural fact a machine
checks (so it cannot widen by intent). This is `exitIsAlwaysZero`'s
discipline applied to the other end of the oracle. -/
def hasDeclareCallDefine (envl : Envelope) (sym : String) : Bool :=
  let calls (es : List Expr) (nm : String) : Bool :=
    es.any fun e => match e with
      | .call callee _ _ _ .. => calleeNameOf callee == nm
      | _ => false
  let defn? := envl.unit.functionDefns.find? (·.name == sym)
  match defn? with
  | none => false
  | some f =>
      let body := (f.body.map LeanModels.C.Stmt.substmts).getD []
      calls envl.unit.exprs sym && calls (body.flatMap LeanModels.C.Stmt.ownExprs) "abort"

/-- The pinned Clang 21.1.8 does not implement GCC's `scalar_storage_order`
attribute. These corpus tests contain a record whose parser-native layout has
bit-fields and whose `main` reaches `abort`; the manifest names the compiler
feature while this shape check keeps the classification tied to the ingested
AST instead of to a filename alone. -/
def hasScalarStorageOrderCompilerShape (envl : Envelope) : Bool :=
  let hasBitfieldRecord := (allDecls envl).any fun d => match d with
    | .record _ _ _ (some layout) _ _ => layout.fields.any (·.bitfield)
    | _ => false
  let hasAbort := envl.unit.exprs.any fun e => match e with
    | .call callee _ _ _ .. =>
        calleeNameOf callee == "abort" || calleeNameOf callee == "__builtin_abort"
    | _ => false
  hasBitfieldRecord && hasAbort

/-- The one execution path shared by the batch scorer and single-file CLI. -/
def runEnvelope (fuel : Nat) (envl : Envelope) : ExecM CVal :=
  let lay := layoutFor envl
  let prog : Program := { fns := envl.unit.functionDefns }
  let prog := { prog with layout := lay }
  let prog := { prog with enumIds := envl.unit.enumBindings }
  do
    if envl.unit.functionDefns.any fun f =>
        f.name == "__cyg_profile_func_enter" || f.name == "__cyg_profile_func_exit" then
      refuseUnsupported "function instrumentation is outside the tier"
    let m ← get
    let (m', stdoutObj) := m.allocZeroed .static_ 1 (some "stdout-stream")
    set m'
    let genv ← setupGlobalsWithIds fuel lay envl.unit.fileScopeObjects [] []
    let senv ← setupStaticsWithIds fuel lay (staticDecls envl) genv.1 genv.2
    let prog := { prog with globals := senv.1, globalIds := senv.2 }
    callByName fuel { prog with stdoutObj := some stdoutObj } "main" []

/-- Run one ingested test: call its `main` with no arguments, from an
empty memory, and read the outcome.

`abort` and `exit` are caught BY NAME, before the libc slice can turn
them into environment refusals, because both are the exit-status oracle
speaking — `docs/c23-goal.md` §1.2. Neither is modelled and neither ever
will be by widening the slice. -/
def stdoutString : List CByte → String
  | [] => ""
  | .conc b :: rest => String.singleton (Char.ofNat b.toNat) ++ stdoutString rest
  | _ :: rest => stdoutString rest

def scoreEnvelope (fuel : Nat) (envl : Envelope)
    (oracleSym : Option String) (oracleWhy : String)
    (expectedStdout : Option String := none) : Verdict :=
  let outcome := ExecM.run Mem.empty (runEnvelope fuel envl)
  match outcome with
  | .ok (.ok value, mem) =>
      if expectedStdout.isSome && stdoutString mem.stdout != expectedStdout.getD "" then
        .failed
      else match value with
        | .int _ 0 | .undef => .passed
        | .int _ _ | .float32 _ | .float64 _ | .ptr _ | .ptrInt _ | .funPtr _ | .aggregate _ _ => .failed
  | .ok (.error .aborted, _) =>
      match oracleSym with
      | some sym =>
          if sym == "scalar_storage_order" then
            if hasScalarStorageOrderCompilerShape envl then
              .oracleTestsCompiler oracleWhy
            else .failed
          else if hasDeclareCallDefine envl sym then .oracleTestsCompiler oracleWhy
          else .failed
      | none => .failed
  | .ok (.error (.libc "abort"), _) =>
      match oracleSym with
      | some sym =>
          if sym == "scalar_storage_order" then
            if hasScalarStorageOrderCompilerShape envl then
              .oracleTestsCompiler oracleWhy
            else .failed
          else if hasDeclareCallDefine envl sym then .oracleTestsCompiler oracleWhy
          else .failed
      | none => .failed
  | .ok (.error (.libc "exit"), _) =>
      if exitIsAlwaysZero envl then .passedViaExit
      else .refusedLibc "exit (an argument is not a literal 0 — which exit was reached is unknown)"
  | .ok (.error (.libc n), _) => .refusedLibc n
  | .ok (.error (.valueUB u), _) => .refusedUB (toString (repr u))
  | .ok (.error (.memUB f), _) => .refusedUB (toString (repr f))
  | .ok (.error (.indeterminateRead ..), _) => .unsupported indeterminateReadMessage
  | .error (.unsupported _ msg _) => .unsupported msg
  | .error .timeout => .timeout

def singleMain (path : String) (fuel : Nat) : IO UInt32 := do
  let contents ← IO.FS.readFile ⟨path⟩
  match parseEnvelopeString contents with
  | .error reason => IO.eprintln s!"ingestion: {reason}"; return 2
  | .ok envl =>
      match ExecM.run Mem.empty (runEnvelope fuel envl) with
      | .ok (.ok (.int _ value), mem) =>
          IO.print (stdoutString mem.stdout); IO.println s!"ok\t{value}"; return 0
      | .ok (.ok .undef, mem) =>
          IO.print (stdoutString mem.stdout); IO.println "ok\t0"; return 0
      | .ok (.ok value, mem) =>
          IO.print (stdoutString mem.stdout); IO.println s!"ok\t{repr value}"; return 0
      | .ok (.error .aborted, _) =>
          IO.eprintln "aborted"; return 5
      | .ok (.error (.libc "exit"), _) =>
          if exitIsAlwaysZero envl then
            IO.println "ok\t0"; return 0
          else
            IO.eprintln "refused\tLeanModels.C.C23.Refusal.libc \"exit\""; return 3
      | .ok (.error (.indeterminateRead ..), _) =>
          IO.eprintln s!"unsupported\t{indeterminateReadMessage}"; return 3
      | .ok (.error reason, _) => IO.eprintln s!"refused\t{repr reason}"; return 3
      | .error .timeout => IO.eprintln "timeout"; return 4
      | .error (.unsupported _ reason _) => IO.eprintln s!"unsupported\t{reason}"; return 3

/-! ## The manifest

`{ "pin": {...}, "tests": [ { "name":…, "status":"parsed"|"rejected"|"absent",
"envelope":…, "why":… } ] }` — produced by `tools/c_corpus_fetch.py`, in
NAME ORDER, and the order is load-bearing: the summary quotes the FIRST
failure, and "first" has to mean something stable. -/

structure Entry where
  name : String
  status : String
  envelope : Option String
  why : String
  /-- The `oracle-tests-compiler` membership, as the PIN records it: the
  symbol the test declare-call-defines, and the citation. `none` for the
  overwhelming majority. See `tools/c_corpus_fetch.py`. -/
  oracleSymbol : Option String
  oracleWhy : String
  expectedStdout : Option String
deriving Inhabited

private def str? (j : Lean.Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

def parseEntry (j : Lean.Json) : Entry :=
  let env := str? j "envelope"
  let otc := (j.getObjVal? "oracle_tests_compiler").toOption
  let sym := (otc.map (str? · "symbol")).getD ""
  let expected := (j.getObjVal? "expected_stdout").toOption.bind (fun v => v.getStr?.toOption)
  { name := str? j "name", status := str? j "status"
    envelope := if env.isEmpty then none else some env
    why := str? j "why"
    oracleSymbol := if sym.isEmpty then none else some sym
    oracleWhy := (otc.map (str? · "citation")).getD ""
    expectedStdout := expected }

def runEntry (fuel : Nat) (e : Entry) : IO Verdict := do
  match e.status, e.envelope with
  | "absent", _ => pure .notFetched
  | "rejected", _ => pure (.notParsed e.why)
  | _, none => pure (.runnerError "manifest says parsed but names no envelope")
  | _, some p =>
      match ← (IO.FS.readFile ⟨p⟩).toBaseIO with
      | .error err => pure (.runnerError s!"cannot read envelope: {toString err}")
      | .ok contents =>
          match parseEnvelopeString contents with
          | .error err => pure (.notIngested err)
          | .ok envl => pure (scoreEnvelope fuel envl e.oracleSymbol e.oracleWhy e.expectedStdout)

/-! ## The summary

**The first failure is printed VERBATIM, in log order.** Not the
lexicographically smallest, not one of a deduplicated set: the first one
the run met. A summary that sorts or uniques its failures answers a
different question from the one a reader asks after a red run, and the
reader cannot tell that it did. -/

def summarise (rows : List (String × Verdict)) : List String := Id.run do
  let mut passed := 0; let mut failed := 0; let mut refUB := 0
  let mut refLibc := 0; let mut unsup := 0; let mut tmo := 0
  let mut notParsed := 0; let mut notIngested := 0
  let mut runnerErr := 0; let mut notFetched := 0; let mut oracleTC := 0
  let mut firstFail : Option (String × Verdict) := none
  for (n, v) in rows do
    match v with
    | .passed | .passedViaExit => passed := passed + 1
    | .oracleTestsCompiler _ => oracleTC := oracleTC + 1
    | .failed =>
        failed := failed + 1
        if firstFail.isNone then firstFail := some (n, v)
    | .refusedUB _ => refUB := refUB + 1
    | .refusedLibc _ => refLibc := refLibc + 1
    | .unsupported _ => unsup := unsup + 1
    | .timeout => tmo := tmo + 1
    | .notParsed _ => notParsed := notParsed + 1
    | .notIngested _ => notIngested := notIngested + 1
    | .runnerError _ => runnerErr := runnerErr + 1
    | .notFetched => notFetched := notFetched + 1
  let total := rows.length
  let scored := passed + failed
  let mut out : List String := []
  out := out ++ [s!"gcc.c-torture {scored}/{total} scored  (passed {passed}, failed {failed})"]
  out := out ++ [s!"  the zeroes, kept apart: refused-unsupported {unsup}, refused-libc {refLibc}, refused-ub {refUB}, oracle-tests-compiler {oracleTC}, timeout {tmo}, not-ingested {notIngested}, not-parsed {notParsed}, runner-error {runnerErr}, not-fetched {notFetched}"]
  match firstFail with
  | none => out := out ++ ["  first failure: none"]
  | some (n, v) =>
      out := out ++ [s!"  FIRST FAILURE (log order, verbatim): {n}  {v.token}  {v.detail}"]
  pure out

def tortureMain (args : List String) : IO UInt32 := do
  match args with
  | ["--single", path] => return ← singleMain path 512
  | ["--single", path, f] => return ← singleMain path (f.toNat?.getD 512)
  | _ => pure ()
  let (onlyName, manifestPath, fuel) : Option String × String × Nat :=
    match args with
    | [p] => (none, p, 64)
    | [p, f] => (none, p, f.toNat?.getD 64)
    | ["--only", name, p] => (some name, p, 64)
    | ["--only", name, p, f] => (some name, p, f.toNat?.getD 64)
    | _ => (none, "", 64)
  if manifestPath.isEmpty then
    IO.eprintln "usage: c-torture-run <manifest.json> [fuel] | --only <name> <manifest.json> [fuel] | --single <envelope.json> [fuel]"
    return 2
  let contents ← IO.FS.readFile ⟨manifestPath⟩
  let j ← IO.ofExcept (Lean.Json.parse contents)
  let tests := (j.getObjValAs? (Array Lean.Json) "tests").toOption.getD #[]
  let mut rows : List (String × Verdict) := []
  for tj in tests do
    let e := parseEntry tj
    if onlyName.isNone || onlyName.getD "" == e.name then
      let v ← runEntry fuel e
      IO.println s!"{e.name}\t{v.token}\t{v.detail}"
      rows := rows ++ [(e.name, v)]
  IO.println "----"
  for l in summarise rows do IO.println l
  return 0

end LeanModels.C.C23.Torture

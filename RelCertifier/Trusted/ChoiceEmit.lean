/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The emitted choice cover

The sets the existential mode choice chose (`OracleAPI.choiceCover`, `RELCERT_CHOICE=1`): per
window and right mode, after a joint segment the chosen successors (`joint`), after a
right-only segment the chosen exits (`repo`), and the chosen hop targets (`hop`), each with
its coverage query `region ∧ ⋀_{q' ∈ S} ¬guard(q')` `unsat` at the time of the search. The
runner rebuilds the queries with `coverageQuery` from the same regions the tool built
(`leftFacts`/`rightFacts` of `certifyWithData`); the bridge reads the verdicts as the chosen
sets' coverage premises.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.InvComponents

namespace RelCertifier.Choice

open RelCertifier RelCertifier.Parse RelCertifier.Run

inductive ChoiceKind where
  | joint | repo | hop
  deriving Repr, DecidableEq, Inhabited

/-- One chosen set: window `mL`, right mode `q`, kind, setting (`pre`: before any joint
segment; immaterial for `joint`), the chosen successor names. -/
structure ChoiceEntryE where
  mL   : String
  q    : String
  kind : ChoiceKind
  pre  : Bool
  S    : List String
  deriving Repr, DecidableEq, Inhabited

structure ChoiceEmitE where
  name    : String
  entries : List ChoiceEntryE
  deriving Repr, DecidableEq, Inhabited

def ChoiceEmitE.empty (name : String) : ChoiceEmitE := ⟨name, []⟩

/-! ## The coverage query, rebuilt -/

variable {n : ℕ}

/-- The tool's `leftFacts pre`: the left evolve domain, the left kept atoms, the row, and
(pre-joint) the left guard. -/
def leftFacts (vars : List String) (n : ℕ) (mL : PMode) (cutL : IForm n)
    (comps : List (ITerm n)) (pre : Bool) : IForm n :=
  let lowL := fun (f : PForm) => (lowerF vars n Side.L f).getD IForm.tt
  let invI := comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt
  let b := IForm.and (IForm.and (lowL mL.evolve) cutL) invI
  if pre then IForm.and b (lowL mL.guard) else b

/-- The tool's `rightFacts`: the right evolve domain and the right kept atoms. -/
def rightFacts (vars : List String) (n : ℕ) (mR : PMode) (cutR : IForm n) : IForm n :=
  IForm.and ((lowerF vars n Side.R mR.evolve).getD IForm.tt) cutR

/-- The region of an entry: `jointEnd` / `repoEnd` / `startReg` of the tool. -/
def regionOfEntry (vars : List String) (n : ℕ) (mL mR : PMode) (cutL cutR : IForm n)
    (comps : List (ITerm n)) (e : ChoiceEntryE) : IForm n :=
  let base := fun (pre : Bool) =>
    IForm.and (leftFacts vars n mL cutL comps pre) (rightFacts vars n mR cutR)
  match e.kind with
  | .joint => base false
  | .repo => base e.pre
  | .hop => IForm.and (base e.pre) ((lowerF vars n Side.R mR.guard).getD IForm.tt)

/-- `region ∧ ⋀_{q' ∈ S} ¬guard(q')` (`coverageUnsat`'s fold). -/
def coverageQuery (region : IForm n) (guards : List (IForm n)) : IForm n :=
  guards.foldl (fun d g => IForm.and d (IForm.neg g)) region

/-! ## Emission -/

def emitEntry (e : ChoiceEntryE) : String :=
  let k := match e.kind with | .joint => ".joint" | .repo => ".repo" | .hop => ".hop"
  s!"⟨\"{e.mL}\", \"{e.q}\", {k}, {e.pre}, {reprStr e.S}⟩"

def emitChoiceE (defname : String) (c : ChoiceEmitE) : String :=
  s!"def {defname} : RelCertifier.Choice.ChoiceEmitE :=\n  ⟨\"{c.name}\", [\n    " ++
    String.intercalate ",\n    " (c.entries.map emitEntry) ++ "]⟩"

end RelCertifier.Choice

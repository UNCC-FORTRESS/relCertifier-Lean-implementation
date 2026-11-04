/-
# The reposition certificate of a right-only node (stage lists)

A right-only segment of mode `q` (paper Definition 3) needs the right to reach a state where
a successor other than `q` is enabled; the right-only flow certificate (paper Definition 5)
says nothing about that. The reposition certificate (paper Definition 7) does, and the tool
establishes it by a stage list (paper Section 6.1, Reposition): stages `(x, θ, up, r)`, each
"while the earlier thresholds are crossed and `x` has not yet crossed `θ`, the field of `x`
moves it toward `θ` at rate at least `r > 0`" (rate, `rateQuery`), each non-last stage "once
crossed, stays crossed" (keep, `keepQuery`), and wherever the last threshold is crossed some
exit's guard holds (landing, `landQueries`; on the crossed region, so a start already past
the threshold switches at once). All are static queries over the node's region `R` (the
paper's `cut_L ∧ cut_R ∧ φ_inv(mL)`, which the right-only cycles keep), like every other
query of the tool. `Proofs/Encoding/Progress.lean` proves that `unsat` answers to these
queries give the reposition premise (`RepoProgress`) of `theorem3_of_coverX`.

The emitted data (`ProgressE`) is what the verdict runner rebuilds the queries from, with the
same builders (`progressQueries`), so the pinned hypotheses are the queries the tool issued.
-/
import RelCertifier.Trusted.Run

namespace RelCertifier.Progress

open RelCertifier RelCertifier.Parse RelCertifier.Run

/-- One stage: coordinate `var` (a right state variable) crosses `theta` upward (`up`) or
downward, at rate at least `rate > 0` while not yet crossed. -/
structure ProgressStageE where
  var   : String
  theta : ℚ
  up    : Bool
  rate  : ℚ
  deriving Repr, DecidableEq, Inhabited

/-- The reposition certificate of right-only node `mR` for left mode `mL`, source setting
`pre` (pre-joint: the left guard is a fact of the region). `exits` are the declared
successors of `mR` other than `mR` (the right-only candidates of paper Section 4.2) whose
guards the landing queries cover. -/
structure ProgressE where
  mL     : String
  mR     : String
  pre    : Bool
  stages : List ProgressStageE
  exits  : List String
  deriving Repr, DecidableEq, Inhabited

/-- Per benchmark. -/
structure ProgressEmitE where
  name  : String
  certs : List ProgressE
  deriving Repr, DecidableEq, Inhabited

/-! ## The queries (pure; the tool checks them, the runner rebuilds them) -/

variable {n : ℕ}

/-- `x ≥ θ` (up) or `x ≤ θ` (down): the crossed fact. -/
def crossed (v : Var n) (st : ProgressStageE) : IForm n :=
  if st.up then .cmp .ge (.var v) (.rat st.theta) else .cmp .le (.var v) (.rat st.theta)

/-- `x < θ` (up) or `x > θ` (down): not yet crossed. -/
def before (v : Var n) (st : ProgressStageE) : IForm n :=
  if st.up then .cmp .lt (.var v) (.rat st.theta) else .cmp .gt (.var v) (.rat st.theta)

/-- `x ≤ θ` (up) or `x ≥ θ` (down): the closure of `before`, the region on which a strict
invariant component's right-only certificate is required (the restricted mode
`mR|¬target` of paper Lemma 4, closed for strict components). -/
def beforeCl (v : Var n) (st : ProgressStageE) : IForm n :=
  if st.up then .cmp .le (.var v) (.rat st.theta) else .cmp .ge (.var v) (.rat st.theta)

/-- The conjunction of the crossed facts of the stages before index `i`. -/
def crossedBefore (vs : List (Var n × ProgressStageE)) (i : ℕ) : IForm n :=
  (vs.take i).foldl (fun d p => IForm.and d (crossed p.1 p.2)) IForm.tt

/-- **rate** (unsat expected): `R ∧ crossed_{<i} ∧ before_i ∧ (ẋ < r | ẋ > −r)`. -/
def rateQuery (R : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (i : ℕ) (v : Var n) (st : ProgressStageE) : IForm n :=
  let dot := fR v.2
  let bad : IForm n := if st.up then .cmp .lt dot (.rat st.rate) else .cmp .gt dot (.rat (-st.rate))
  IForm.and (IForm.and (IForm.and R (crossedBefore vs i)) (before v st)) bad

/-- **keep** (unsat expected): `R ∧ crossed_{<i} ∧ (x ≤ θ ∧ ẋ < 0 | x ≥ θ ∧ ẋ > 0)`: at or
below (above) the threshold the field does not move away, so the crossed fact is kept. -/
def keepQuery (R : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (i : ℕ) (v : Var n) (st : ProgressStageE) : IForm n :=
  let dot := fR v.2
  let side : IForm n := if st.up then .cmp .le (.var v) (.rat st.theta) else .cmp .ge (.var v) (.rat st.theta)
  let bad : IForm n := if st.up then .cmp .lt dot (.rat 0) else .cmp .gt dot (.rat 0)
  IForm.and (IForm.and (IForm.and R (crossedBefore vs i)) side) bad

/-- `x = θ`: the crossing line. -/
def onLine (v : Var n) (st : ProgressStageE) : IForm n := .cmp .eq (.var v) (.rat st.theta)

/-- **land** (each unsat expected). The last stage's coordinate first satisfies its crossed
fact either on the crossing line (some point of the run with `x = θ`, by continuity) or at the
node's start, already crossed. At every such state of the region some exit's guard must hold:
* `R ∧ x_last = θ_last ∧ ⋀ ¬guard(e)`;
* `R ∧ guard(q) ∧ crossed_last ∧ ⋀ ¬guard(e)`.
Neither needs the helper stages' crossed facts: those only feed the last stage's rate. -/
def landQueries (R guardq : IForm n) (v : Var n) (st : ProgressStageE)
    (guards : List (IForm n)) : List (IForm n) :=
  let neg := fun (base : IForm n) => guards.foldl (fun d g => IForm.and d (IForm.neg g)) base
  [neg (IForm.and R (onLine v st)), neg (IForm.and (IForm.and R guardq) (crossed v st))]

/-- **The stage-list shapes the kernel accepts** (`Emitted.certOK`): one stage, or two stages
(a helper, then the landing stage), each stage in either direction (paper Appendix B.3,
`repoProgress_two_ud/du/dd_reg`). The search (`OracleAPI.checkProgress`) returns a stage list
only when it passes this test, so no shape the kernel rejects is emitted. -/
def shapeOK (sts : List ProgressStageE) : Bool := sts.length == 1 || sts.length == 2

/-- The queries of a resolved stage list (one or two stages): per stage its rate query and
(non-last) keep query, then the landing queries. -/
def stageQueries (R guardq : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (guards : List (IForm n)) : Option (List (IForm n)) :=
  match vs with
  | [(v, st)] => some ([rateQuery R fR [(v, st)] 0 v st] ++ landQueries R guardq v st guards)
  | [(w, sth), (v, st)] =>
      some ([rateQuery R fR [(w, sth), (v, st)] 0 w sth, keepQuery R fR [(w, sth), (v, st)] 0 w sth,
        rateQuery R fR [(w, sth), (v, st)] 1 v st] ++ landQueries R guardq v st guards)
  | _ => none

/-- The queries of a reposition certificate: its stages resolved to right coordinates, its exits' guards
and the node's guard lowered. `none` if a variable or a guard does not lower, or the stage
list is not one or two stages. -/
def progressQueries (vars : List String) (R guardq : IForm n) (fR : Fin n → ITerm n)
    (guardOf : String → Option (IForm n)) (c : ProgressE) : Option (List (IForm n)) := do
  let vs ← c.stages.mapM (fun st => (resolveVar vars n Side.R st.var).map (fun v => (v, st)))
  let guards ← c.exits.mapM guardOf
  stageQueries R guardq fR vs guards

/-! ## Emission -/

def emitStage (st : ProgressStageE) : String :=
  s!"⟨\"{st.var}\", ({st.theta.num} : ℚ) / {st.theta.den}, {st.up}, ({st.rate.num} : ℚ) / {st.rate.den}⟩"

def emitProgressE (defname : String) (c : ProgressEmitE) : String :=
  let one := fun (p : ProgressE) =>
    s!"⟨\"{p.mL}\", \"{p.mR}\", {p.pre}, [" ++ String.intercalate ", " (p.stages.map emitStage) ++
      "], " ++ reprStr p.exits ++ "⟩"
  s!"def {defname} : RelCertifier.Progress.ProgressEmitE :=\n  ⟨\"{c.name}\", [\n    " ++
    String.intercalate ",\n    " (c.certs.map one) ++ "]⟩"

end RelCertifier.Progress

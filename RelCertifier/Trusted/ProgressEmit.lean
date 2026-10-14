/-
# The progress certificate of a right-only (reposition) node

A right-only segment of mode `q` is sound only if the right actually reaches a state where a
declared non-self successor is enabled; the reposition flow certificate (certificate 3) says
nothing about that. The **progress certificate** does, by a staged rate argument: a list of
stages `(x, θ, up, r)`, each "while the earlier thresholds are crossed and `x` has not yet
crossed `θ`, the field of `x` moves it toward `θ` at rate at least `r > 0`" (`rateQuery`), each
non-last stage "once crossed, stays crossed" (`keepQuery`), and wherever the last threshold is
crossed some exit's guard holds (`landQuery`; on the crossed region, so a start already past the
threshold switches at once). All three are static queries over the node's region (the facts
the reposition flow preserves), the shape of every other certificate of the tool. `Proofs/Encoding/Progress.lean` proves that `unsat` answers to these
queries give the reposition-progress premise of `theorem3_of_coverX`.

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

/-- The certificate of reposition node `mR` in window `mL`, setting `pre` (pre-joint:
the left guard is a fact of the region). `exits` are the declared non-self successors the
landing covers. -/
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

/-- The queries of a certificate, in order: per stage its rate query and (non-last) keep
query, then the landing queries. `none` if a variable or an exit guard does not lower. -/
def progressQueries (vars : List String) (R : IForm n) (fR : Fin n → ITerm n)
    (guardOf : String → Option (IForm n)) (c : ProgressE) : Option (List (IForm n)) := do
  let vs ← c.stages.mapM (fun st => (resolveVar vars n Side.R st.var).map (fun v => (v, st)))
  let guards ← c.exits.mapM guardOf
  let guardq ← guardOf c.mR
  if vs.isEmpty then none
  let last := vs.length - 1
  let perStage := (List.range vs.length).flatMap (fun i =>
    match vs[i]? with
    | some (v, st) =>
        rateQuery R fR vs i v st :: (if i < last then [keepQuery R fR vs i v st] else [])
    | none => [])
  match vs[last]? with
  | some (v, st) => pure (perStage ++ landQueries R guardq v st guards)
  | none => none

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

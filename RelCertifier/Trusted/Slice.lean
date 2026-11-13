/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Per-row hypothesis slicing of the flow queries (`RELCERT_SLICE_HOPS`, `docs/HYP-SLICING.md`)

A flow query of a row `g` carries, as its domain, every hypothesis established so far (the
evolve boxes, the mode facts, the rows of earlier rounds). On wide models the full set is more
than Z3 handles in its budget while a small slice of it is provable. With the knob
`RELCERT_SLICE_HOPS=k` the tool keeps only the hypotheses within `k` variable-sharing hops of
the row's goal variables (`goalVars`: the variables of `g` and of its Lie derivative):

* hop 0: the rows (conjuncts reading two or more variables) whose variables intersect the goal
  set;
* hop `j+1`: the rows sharing a variable with a row kept at hop `j`;
* the boxes (conjuncts reading at most one variable) of every kept variable are always kept.

`sliceDom` replaces every dropped conjunct of the domain's `and` tree by `tt` IN PLACE (the
tree shape is kept, so the sliced domain is a sub-conjunction of the full one leaf by leaf).
With the knob unset (`sliceDomOpt none`) the domain is untouched and the printed query is
byte-identical to the unsliced tool's.

A `sat` answer on a sliced query is inconclusive for the full one (a dropped hypothesis can
admit a spurious model), so the tool ESCALATES: a row is tried at hop `k`, then `k+1`, …, and
on the full domain last (`sliceFlowLevels`); `unsat` at any level is the verdict, `sat` or
`unknown` at a sliced level moves to the next, and only the full level classifies (`sat`
there FAILS the component, `unknown` there is inconclusive). `RELCERT_SLICE_HOPS=k` means
"start at hop `k`".

Soundness (`sliceDom_weakens`, `sliceLevels_weakens`): every level is implied by the full
domain, so an `unsat` answer on any level's query is an `unsat` answer on a query implied by
the row's full query, which is exactly the sliced verdict `Z3Unsat` of `Trusted/Oracle.lean`
(`Z3Unsat_of_level`; `Z3Unsat_of_sliced` is the one-level form). The same function serves the
tool (`OracleAPI.checkSeg`, `checkDynRepo`) and the runners (`VerdictsV2/ModalX`, `ModalDynX`,
`ModalXStrict`), so a pinned group's members ARE the level texts, in the tool's order.
-/
import RelCertifier.Trusted.Smt
import RelCertifier.Trusted.Oracle

namespace RelCertifier

open DL

/-! ## Variables of a term, zero products dropped -/

/-- A term that is syntactically zero (`0`, sums of zeros, products with a zero factor): the
Lie derivative `ilieDeriv` carries `0 * f_i` for every coordinate the row does not read, and
those read nothing. -/
def ITerm.isZero {n : ℕ} : ITerm n → Bool
  | .rat q => q == 0
  | .var _ => false
  | .bin .add a b => a.isZero && b.isZero
  | .bin .sub a b => a.isZero && b.isZero
  | .bin .mul a b => a.isZero || b.isZero

/-- The variables a term reads (zero products dropped). -/
def ITerm.vars {n : ℕ} : ITerm n → List (Var n)
  | .var v => [v]
  | .rat _ => []
  | .bin .mul a b => if a.isZero || b.isZero then [] else a.vars ++ b.vars
  | .bin .add a b => a.vars ++ b.vars
  | .bin .sub a b => a.vars ++ b.vars

/-- The variables a formula reads. -/
def IForm.vars {n : ℕ} : IForm n → List (Var n)
  | .tt => []
  | .cmp _ a b => a.vars ++ b.vars
  | .neg f => f.vars
  | .and a b => a.vars ++ b.vars

/-- The conjuncts of a domain: the leaves of its `and` tree (`tt` leaves dropped). -/
def IForm.leaves {n : ℕ} : IForm n → List (IForm n)
  | .and a b => a.leaves ++ b.leaves
  | .tt => []
  | f => [f]

/-- The seed of the slice: the row's own variables and those its Lie derivative reads. -/
def goalVars {n : ℕ} (g gdot : ITerm n) : List (Var n) := g.vars ++ gdot.vars

/-! ## The hop closure -/

/-- Two variable lists share a variable. -/
def varsMeet {n : ℕ} (a b : List (Var n)) : Bool := a.any (fun v => b.contains v)

/-- The variables of a conjunct, duplicates removed. -/
def IForm.varSet {n : ℕ} (f : IForm n) : List (Var n) := f.vars.eraseDups

/-- A row reads two or more variables; a box at most one. -/
def IForm.isRow {n : ℕ} (f : IForm n) : Bool := 2 ≤ f.varSet.length

/-- One hop: the kept variables plus those of every row meeting them. -/
def hopStep {n : ℕ} (rows : List (List (Var n))) (K : List (Var n)) : List (Var n) :=
  K ++ (rows.filter (fun r => varsMeet r K)).flatten

/-- The variables reached after `k` hops from the seed. -/
def hopVars {n : ℕ} (rows : List (List (Var n))) : ℕ → List (Var n) → List (Var n)
  | 0, V => V
  | k + 1, V => hopStep rows (hopVars rows k V)

/-- Replace every leaf the predicate rejects by `tt`, in place. -/
def IForm.pruneTT {n : ℕ} (keep : IForm n → Bool) : IForm n → IForm n
  | .and a b => .and (a.pruneTT keep) (b.pruneTT keep)
  | .tt => .tt
  | .cmp op a b => if keep (.cmp op a b) then .cmp op a b else .tt
  | .neg f => if keep (.neg f) then .neg f else .tt

/-- **The slice of a domain at `k` hops from the seed `V`.** A row is kept when it meets the
variables reached after `k` hops; a box when its variable is among the kept variables (the seed,
the reached ones and those of the kept rows). -/
def sliceDom {n : ℕ} (k : ℕ) (V : List (Var n)) (dom : IForm n) : IForm n :=
  let rows := (dom.leaves.filter IForm.isRow).map IForm.varSet
  let K := hopVars rows k V
  let Kfin := hopStep rows K
  dom.pruneTT (fun c =>
    if c.isRow then varsMeet c.varSet K else c.varSet.all (fun v => Kfin.contains v))

/-- The knob: `none` leaves the domain untouched (the unsliced tool), `some k` slices. -/
def sliceDomOpt {n : ℕ} : Option ℕ → List (Var n) → IForm n → IForm n
  | none, _, dom => dom
  | some k, V, dom => sliceDom k V dom

/-- The slice of a flow-query domain for the row `g` with Lie derivative `gdot`: the function
the tool and the runners share. -/
def sliceFlowDom {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom : IForm n) : IForm n :=
  sliceDomOpt k (goalVars g gdot) dom

/-! ## The escalation levels

A `sat` answer on a sliced query is inconclusive for the full one (dropping hypotheses can
create spurious models), so a flow query is tried level by level: the slice at hop `k`, then
`k+1`, …, and the full domain last. `unsat` at any level is the verdict; only the full level
classifies (`sat` there is a FAIL, `unknown` there is inconclusive). The tool and the pins build
the levels with the same function (`sliceFlowLevels`), so a group's members are exactly the
texts the tool sends, in the order it sends them. -/

/-- The sliced levels from hop `j`, labelled by their hop: the slice at `j`, then at `j+1`, …
while each adds a conjunct, stopping before a level that is the full domain or repeats the
previous one (the hop closure is saturated). `fuel` bounds the recursion (one more than the
number of conjuncts suffices: every kept level adds at least one). -/
def sliceLevelsGo {n : ℕ} (V : List (Var n)) (dom : IForm n) :
    ℕ → ℕ → Option (IForm n) → List (Option ℕ × IForm n)
  | _, 0, _ => []
  | j, fuel + 1, prev =>
      let d := sliceDom j V dom
      if d = dom ∨ prev = some d then []
      else (some j, d) :: sliceLevelsGo V dom (j + 1) fuel (some d)

/-- **The escalation levels of a domain**, labelled: with the knob `some k` the sliced levels
from hop `k` (`sliceLevelsGo`) followed by the full domain (label `none`); with the knob unset
the full domain alone (the unsliced tool, byte-identical queries). -/
def sliceLevelsL {n : ℕ} (k : Option ℕ) (V : List (Var n)) (dom : IForm n) :
    List (Option ℕ × IForm n) :=
  match k with
  | none => [(none, dom)]
  | some k => sliceLevelsGo V dom k (dom.leaves.length + 1) none ++ [(none, dom)]

/-- The levels' domains. -/
def sliceLevels {n : ℕ} (k : Option ℕ) (V : List (Var n)) (dom : IForm n) : List (IForm n) :=
  (sliceLevelsL k V dom).map (·.2)

/-- The labelled levels of a flow-query domain for the row `g` with Lie derivative `gdot`
(the tool's loop). -/
def sliceFlowLevelsL {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom : IForm n) :
    List (Option ℕ × IForm n) :=
  sliceLevelsL k (goalVars g gdot) dom

/-- The levels of a flow-query domain (the pins' groups): the function the tool and the
runners share. -/
def sliceFlowLevels {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom : IForm n) :
    List (IForm n) :=
  sliceLevels k (goalVars g gdot) dom

theorem sliceFlowLevels_eq_map {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom : IForm n) :
    sliceFlowLevels k g gdot dom = (sliceFlowLevelsL k g gdot dom).map (·.2) := rfl

/-- With the knob unset the only level is the full domain. -/
theorem sliceFlowLevels_none {n : ℕ} (g gdot : ITerm n) (dom : IForm n) :
    sliceFlowLevels none g gdot dom = [dom] := rfl

/-- Hypothesis count of a domain (its non-`tt` leaves), for the log line. -/
def IForm.hypCount {n : ℕ} (f : IForm n) : ℕ := f.leaves.length

/-- Distinct variable count of a formula, for the log line. -/
def IForm.varCount {n : ℕ} (f : IForm n) : ℕ := f.varSet.length

/-- The knob, read once per runner: `RELCERT_SLICE_HOPS=k` (a natural number), else `none`. -/
def sliceHopsFromEnv : IO (Option ℕ) := do
  pure ((← IO.getEnv "RELCERT_SLICE_HOPS").bind String.toNat?)

/-! ## Soundness: the slice is implied by the full domain -/

theorem pruneTT_weakens {n : ℕ} (keep : IForm n → Bool) (f : IForm n) (σ : State (Var n))
    (h : Formula.sat f.toHost σ) : Formula.sat (f.pruneTT keep).toHost σ := by
  induction f with
  | tt => simp [IForm.pruneTT, IForm.toHost, Formula.sat]
  | cmp op a b =>
      unfold IForm.pruneTT
      split
      · exact h
      · simp [IForm.toHost, Formula.sat]
  | neg f _ =>
      unfold IForm.pruneTT
      split
      · exact h
      · simp [IForm.toHost, Formula.sat]
  | and a b iha ihb =>
      simp only [IForm.pruneTT, IForm.toHost, Formula.sat] at h ⊢
      exact ⟨iha h.1, ihb h.2⟩

/-- **Monotonicity of the slice**: a state in the full domain is in the sliced one. -/
theorem sliceDom_weakens {n : ℕ} (k : ℕ) (V : List (Var n)) (dom : IForm n) (σ : State (Var n))
    (h : Formula.sat dom.toHost σ) : Formula.sat (sliceDom k V dom).toHost σ :=
  pruneTT_weakens _ dom σ h

theorem sliceDomOpt_weakens {n : ℕ} (k : Option ℕ) (V : List (Var n)) (dom : IForm n)
    (σ : State (Var n)) (h : Formula.sat dom.toHost σ) :
    Formula.sat (sliceDomOpt k V dom).toHost σ := by
  cases k with
  | none => exact h
  | some k => exact sliceDom_weakens k V dom σ h

theorem sliceFlowDom_weakens {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom : IForm n)
    (σ : State (Var n)) (h : Formula.sat dom.toHost σ) :
    Formula.sat (sliceFlowDom k g gdot dom).toHost σ :=
  sliceDomOpt_weakens k _ dom σ h

/-- A query over the sliced domain is implied by the same query over the full domain. -/
theorem and_sliceFlowDom_weakens {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom G : IForm n)
    (σ : State (Var n)) (h : Formula.sat (IForm.and dom G).toHost σ) :
    Formula.sat (IForm.and (sliceFlowDom k g gdot dom) G).toHost σ := by
  simp only [IForm.toHost, Formula.sat] at h ⊢
  exact ⟨sliceFlowDom_weakens k g gdot dom σ h.1, h.2⟩

/-- **The sliced verdict of a flow query.** An `unsat` answer on the query over the sliced
domain (what the runner prints under the knob) is the sliced verdict `Z3Unsat` of the query over
the full domain (what the flow packs assume). With `k = none` the two queries coincide. -/
theorem Z3Unsat_of_sliced {n : ℕ} {k : Option ℕ} {g gdot : ITerm n} {dom G : IForm n}
    (h : z3solve (IForm.and (sliceFlowDom k g gdot dom) G).toHost = Verdict.unsat) :
    Z3Unsat (IForm.and dom G).toHost :=
  Z3Unsat.of_weaker (and_sliceFlowDom_weakens k g gdot dom G) h

/-! ## Soundness of the levels: every level is implied by the full domain -/

/-- Every sliced level is a slice of the full domain. -/
theorem mem_sliceLevelsGo {n : ℕ} (V : List (Var n)) (dom : IForm n) (j fuel : ℕ)
    (prev : Option (IForm n)) (x : Option ℕ × IForm n) (hx : x ∈ sliceLevelsGo V dom j fuel prev) :
    ∃ j', x.2 = sliceDom j' V dom := by
  induction fuel generalizing j prev with
  | zero => simp [sliceLevelsGo] at hx
  | succ fuel ih =>
      simp only [sliceLevelsGo] at hx
      split at hx
      · simp at hx
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨j, rfl⟩
        · exact ih _ _ hx

/-- Every level is the full domain or a slice of it. -/
theorem mem_sliceLevelsL {n : ℕ} (k : Option ℕ) (V : List (Var n)) (dom : IForm n)
    (x : Option ℕ × IForm n) (hx : x ∈ sliceLevelsL k V dom) :
    x.2 = dom ∨ ∃ j', x.2 = sliceDom j' V dom := by
  cases k with
  | none => simp only [sliceLevelsL, List.mem_singleton] at hx; subst hx; exact Or.inl rfl
  | some k =>
      simp only [sliceLevelsL, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inr (mem_sliceLevelsGo V dom k _ none x hx)
      · exact Or.inl rfl

/-- **Monotonicity of the levels**: a state in the full domain is in every level. -/
theorem sliceLevels_weakens {n : ℕ} (k : Option ℕ) (V : List (Var n)) (dom d : IForm n)
    (hd : d ∈ sliceLevels k V dom) (σ : State (Var n)) (h : Formula.sat dom.toHost σ) :
    Formula.sat d.toHost σ := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
  rcases mem_sliceLevelsL k V dom x hx with h2 | ⟨j', h2⟩
  · rw [h2]; exact h
  · rw [h2]; exact sliceDom_weakens j' V dom σ h

theorem sliceFlowLevels_weakens {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom d : IForm n)
    (hd : d ∈ sliceFlowLevels k g gdot dom) (σ : State (Var n))
    (h : Formula.sat dom.toHost σ) : Formula.sat d.toHost σ :=
  sliceLevels_weakens k _ dom d hd σ h

/-- A query over a level is implied by the same query over the full domain. -/
theorem and_sliceFlowLevels_weakens {n : ℕ} (k : Option ℕ) (g gdot : ITerm n) (dom d G : IForm n)
    (hd : d ∈ sliceFlowLevels k g gdot dom) (σ : State (Var n))
    (h : Formula.sat (IForm.and dom G).toHost σ) : Formula.sat (IForm.and d G).toHost σ := by
  simp only [IForm.toHost, Formula.sat] at h ⊢
  exact ⟨sliceFlowLevels_weakens k g gdot dom d hd σ h.1, h.2⟩

/-- **The verdict of an escalated flow query.** An `unsat` answer on the query over any of its
levels (what the tool sends, hop `k`, `k+1`, …, the full domain) is the sliced verdict `Z3Unsat`
of the query over the full domain (what the flow packs assume). With `k = none` the only level
is the full domain. -/
theorem Z3Unsat_of_level {n : ℕ} {k : Option ℕ} {g gdot : ITerm n} {dom d G : IForm n}
    (hd : d ∈ sliceFlowLevels k g gdot dom)
    (h : z3solve (IForm.and d G).toHost = Verdict.unsat) :
    Z3Unsat (IForm.and dom G).toHost :=
  Z3Unsat.of_weaker (and_sliceFlowLevels_weakens k g gdot dom d G hd) h

end RelCertifier

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Progress verdicts: the queries, rebuilt, and their meaning

`progressQueriesOf` rebuilds the progress certificate's queries from the emitted IR, the
extended cut certificate and the emitted certificate (`ProgressE`), with the region the tool
uses (`leftFacts ∧ rightFacts`: the left evolve domain, the left kept atoms, the invariant row,
pre-joint the left guard; the right evolve domain and the right kept atoms). The runner prints
them and owes one `unsat` per query. `rate_of_unsat`, `keep_of_unsat`, `line_of_unsat` and
`start_of_unsat` read an `unsat` answer as the semantic fact the progress lemmas
(`Proofs/Encoding/Progress.lean`) consume, at the host denotation of the region.
-/
import RelCertifier.VerdictsV2.ModalDynX
import RelCertifier.Trusted.ProgressEmit
import RelCertifier.Trusted.JointVars

namespace RelCertifier.Progress

open DL Parse RelCertifier RelCertifier.Oracle RelCertifier.Run

variable {n : ℕ}

/-- The region of reposition node `m` in window `l` (setting `pre`), as the tool builds it. -/
def regionOf (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ) (pre : Bool) (l m : ℕ) :
    Option (IForm n) := do
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mL := p.L.modes.getD l dm
  let mR := p.R.modes.getD m dm
  let comps ← invComponents vars n (p.invariants.getD invRow ("", PForm.tt)).2
  let invI := comps.foldl (fun d g => IForm.and d (IForm.cmp .le g (.rat 0))) IForm.tt
  let evL ← lowerF vars n Side.L mL.evolve
  let evR ← lowerF vars n Side.R mR.evolve
  let aL ← ((cutAtomsOfX cX.L mL.name).map (·.atom)).mapM (lowerF vars n Side.L)
  let aR ← ((cutAtomsOfX cX.R mR.name).map (·.atom)).mapM (lowerF vars n Side.R)
  let gL ← lowerF vars n Side.L mL.guard
  let leftFacts := IForm.and (IForm.and (IForm.and evL (icutF aL)) invI)
    (if pre then gL else IForm.tt)
  pure (IForm.and leftFacts (IForm.and evR (icutF aR)))

/-- The certificate's queries, rebuilt. -/
def progressQueriesOf (p : PProblem) (cX : EvolStrengtheningX) (n invRow : ℕ) (l m : ℕ)
    (c : ProgressE) : Option (List (IForm n)) := do
  let vars := p.L.stateVars
  let dm : PMode := ⟨"", [], .tt, .tt, []⟩
  let mR := p.R.modes.getD m dm
  let R ← regionOf p cX n invRow c.pre l m
  let fR ← dynOf vars n Side.R mR
  let gq ← lowerF vars n Side.R mR.guard
  let guardOf := fun (nm : String) =>
    (p.R.modes.find? (·.name == nm)).bind (fun md => lowerF vars n Side.R md.guard)
  progressQueries vars R gq fR guardOf c

/-- The row index of a mode name in a mode list (sentinel: the length). -/
def modeIdx (ms : List PMode) (nm : String) : Nat := ms.findIdx (·.name == nm)

/-- The invariant row of a window: the left mode's own when rows are per mode, else row 0. -/
def invRowOf (p : PProblem) (l : ℕ) : ℕ := if p.invariants.length > l then l else 0

/-- **The progress verdict of one emitted certificate**: the runner's rebuild succeeds
(`progressQueriesOf` at the runner's indices; a failed rebuild is a SKIP, non-green) and every
rebuilt query is `unsat`. -/
def ProgressVerd (p : PProblem) (cX : EvolStrengtheningX) (n : ℕ) (c : ProgressE) : Prop :=
  ∃ qs, progressQueriesOf p cX n (invRowOf p (modeIdx p.L.modes c.mL)) (modeIdx p.L.modes c.mL)
    (modeIdx p.R.modes c.mR) c = some qs ∧ ∀ q ∈ qs, z3solve q.toHost = Verdict.unsat

/-! ## Reading `unsat` answers -/

theorem sat_toHost_and (a b : IForm n) (y : State (Var n)) :
    Formula.sat (IForm.and a b).toHost y ↔ Formula.sat a.toHost y ∧ Formula.sat b.toHost y :=
  Iff.rfl

theorem sat_toHost_neg (a : IForm n) (y : State (Var n)) :
    Formula.sat (IForm.neg a).toHost y ↔ ¬ Formula.sat a.toHost y := Iff.rfl

theorem sat_crossedBefore (vs : List (Var n × ProgressStageE)) (i : ℕ) (y : State (Var n)) :
    Formula.sat (crossedBefore vs i).toHost y ↔
      ∀ p ∈ vs.take i, Formula.sat (crossed p.1 p.2).toHost y := by
  unfold crossedBefore
  generalize vs.take i = l
  induction l using List.reverseRecOn with
  | nil => simp [IForm.toHost, Formula.sat]
  | append_singleton l a ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [sat_toHost_and, ih, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ p (hp | rfl)
        · exact h1 p hp
        · exact h2
      · intro h
        exact ⟨fun p hp => h p (Or.inl hp), h a (Or.inr rfl)⟩

theorem sat_crossed_up (v : Var n) (st : ProgressStageE) (hup : st.up = true)
    (y : State (Var n)) : Formula.sat (crossed v st).toHost y ↔ (st.theta : ℝ) ≤ y v := by
  simp [crossed, hup, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

theorem sat_before_up (v : Var n) (st : ProgressStageE) (hup : st.up = true)
    (y : State (Var n)) : Formula.sat (before v st).toHost y ↔ y v < (st.theta : ℝ) := by
  simp [before, hup, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

theorem sat_crossed_down (v : Var n) (st : ProgressStageE) (hup : st.up = false)
    (y : State (Var n)) : Formula.sat (crossed v st).toHost y ↔ y v ≤ (st.theta : ℝ) := by
  simp [crossed, hup, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

theorem sat_before_down (v : Var n) (st : ProgressStageE) (hup : st.up = false)
    (y : State (Var n)) : Formula.sat (before v st).toHost y ↔ (st.theta : ℝ) < y v := by
  simp [before, hup, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

theorem sat_onLine (v : Var n) (st : ProgressStageE) (y : State (Var n)) :
    Formula.sat (onLine v st).toHost y ↔ y v = (st.theta : ℝ) := by
  simp [onLine, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval]

/-- **rate** (upward): on the region, under the earlier crossed facts and before the
threshold, the field is at least the rate. -/
theorem rate_of_unsat (R : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (i : ℕ) (v : Var n) (st : ProgressStageE) (hup : st.up = true)
    (hz : z3solve (rateQuery R fR vs i v st).toHost = Verdict.unsat) :
    ∀ y, Formula.sat R.toHost y → Formula.sat (crossedBefore vs i).toHost y →
      y v < (st.theta : ℝ) → (st.rate : ℝ) ≤ Term.eval (fR v.2).toHost y := by
  intro y hR hC hb
  have hns := z3_unsat_sound hz y
  by_contra hlt
  push Not at hlt
  refine hns ?_
  unfold rateQuery
  simp only [hup, if_true]
  refine ⟨⟨⟨hR, hC⟩, (sat_before_up v st hup y).mpr hb⟩, ?_⟩
  simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using hlt

/-- **rate** (downward): on the region, under the earlier crossed facts and above the
threshold, the field is at most the negated rate. -/
theorem rate_of_unsat_down (R : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (i : ℕ) (v : Var n) (st : ProgressStageE) (hup : st.up = false)
    (hz : z3solve (rateQuery R fR vs i v st).toHost = Verdict.unsat) :
    ∀ y, Formula.sat R.toHost y → Formula.sat (crossedBefore vs i).toHost y →
      (st.theta : ℝ) < y v → Term.eval (fR v.2).toHost y ≤ -(st.rate : ℝ) := by
  intro y hR hC hb
  have hns := z3_unsat_sound hz y
  by_contra hlt
  push Not at hlt
  refine hns ?_
  unfold rateQuery
  simp only [hup, Bool.false_eq_true, if_false]
  refine ⟨⟨⟨hR, hC⟩, (sat_before_down v st hup y).mpr hb⟩, ?_⟩
  simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using hlt

/-- **keep** (upward): at or below the threshold the field is nonnegative. -/
theorem keep_of_unsat (R : IForm n) (fR : Fin n → ITerm n) (vs : List (Var n × ProgressStageE))
    (i : ℕ) (v : Var n) (st : ProgressStageE) (hup : st.up = true)
    (hz : z3solve (keepQuery R fR vs i v st).toHost = Verdict.unsat) :
    ∀ y, Formula.sat R.toHost y → Formula.sat (crossedBefore vs i).toHost y →
      y v ≤ (st.theta : ℝ) → 0 ≤ Term.eval (fR v.2).toHost y := by
  intro y hR hC hb
  have hns := z3_unsat_sound hz y
  by_contra hlt
  push Not at hlt
  refine hns ?_
  unfold keepQuery
  simp only [hup, if_true]
  refine ⟨⟨⟨hR, hC⟩, ?_⟩, ?_⟩
  · simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using hb
  · simpa [IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval] using hlt

/-- The landing conjunction: some exit's guard holds. -/
theorem land_of_unsat (base : IForm n) (guards : List (IForm n))
    (hz : z3solve (guards.foldl (fun d g => IForm.and d (IForm.neg g)) base).toHost
      = Verdict.unsat) :
    ∀ y, Formula.sat base.toHost y → ∃ g ∈ guards, Formula.sat g.toHost y := by
  intro y hb
  have hns := z3_unsat_sound hz y
  by_contra hno
  push Not at hno
  refine hns ?_
  clear hns hz
  induction guards using List.reverseRecOn with
  | nil => simpa using hb
  | append_singleton gs g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨ih (fun g' hg' => hno g' (List.mem_append_left _ hg')), ?_⟩
      exact hno g (List.mem_append_right _ (List.mem_singleton_self g))

end RelCertifier.Progress

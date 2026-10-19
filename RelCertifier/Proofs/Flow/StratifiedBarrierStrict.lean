/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Stratified differential cuts with strict components (extension `strict-atoms`)

`StratifiedBarrier` proves the stratified discipline for `≤ 0` components. Here the
components are FLAGGED (`ts : List (Bool × Term)`, `HoldsAt`): a strict component must be
kept `< 0`, the others `≤ 0`. Mixed masks are handled stratum by stratum:

* the NARROWING (the antecedent of every stratum's query) stays the closure
  `bigLe (prefix)` / `strataDomHost D (prefix)`, exactly the tool's query domains: a strict
  prefix component is only assumed `≤ 0` (its strict truth implies that). This also keeps
  the route-B boundary query non-vacuous: its antecedent never contains `g < 0`;
* the CONCLUSION of a strict stratum is `< 0`, produced by route A or B only
  (`flow_cert_sound_lt`, `flow_cert_sound_strict_lt`); route C does not preserve `< 0`
  (`routeC_counterexample`), so a strict component's verdict group is [A, B].

`stratified_barrier_soundS`, `segPresAllS_from_strata_verdicts'`; with every flag `false`
the verdict pack and the preservation are the existing ones
(`verdXCoreS_allFalse`, `segPresAllOnS_allFalse`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Flow.StratifiedBarrier
import RelCertifier.Proofs.Flow.DIStrictOpen
import RelCertifier.Proofs.Flow.StrictAtoms

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-! ## The flagged stratified assembly -/

/-- The prefix of a flagged list as plain components (the narrowing is the closure). -/
theorem take_map_snd (ts : List (Bool × Term (Var n))) (i : ℕ) :
    (ts.take i).map Prod.snd = (ts.map Prod.snd).take i := by
  rw [List.map_take]

/-- **Stratified differential cuts with strict components.** Each stratum's certificate
concludes the component's own flag (`HoldsAt`), over the ode narrowed by the CLOSURE of
its prefix. From a start where every flagged component holds, every flagged component
holds at every time along every run of the un-narrowed ode. -/
theorem stratified_barrier_soundS (sys : ODESystem (Var n)) (D : Formula (Var n))
    (ts : List (Bool × Term (Var n)))
    (hcert : ∀ i (hi : i < ts.length), ∀ ν', HoldsAt ts[i].1 ts[i].2 ν' →
      ∀ ω, Program.sem (Program.ode sys (Formula.and D (bigLe ((ts.take i).map Prod.snd))))
        ν' ω → HoldsAt ts[i].1 ts[i].2 ω)
    {ν : State (Var n)} (hinit : ∀ c ∈ ts, HoldsAt c.1 c.2 ν)
    {r : ℝ} {Φ : ℝ → State (Var n)} (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s)
    (hmask : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ s x = ν x)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ s)) :
    ∀ i (hi : i < ts.length), ∀ t ∈ Set.Icc (0:ℝ) r, HoldsAt ts[i].1 ts[i].2 (Φ t) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi t ht
      have hpre : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ g ∈ (ts.take i).map Prod.snd,
          Term.eval g (Φ s) ≤ 0 := by
        intro s hs g hg
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
        obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hc
        rw [List.getElem_take] at hjc
        have hjlen : j < ts.length := by
          have := List.length_take_le i ts
          omega
        rw [← hjc]
        exact (ih j (by
          have := hj
          rw [List.length_take] at this
          omega) hjlen s hs).le
      have hrun := sem_ode_refine ((ts.take i).map Prod.snd) hr hΦ0 hder hmask hdom hpre ht
      exact hcert i hi ν (hinit _ (List.getElem_mem hi)) (Φ t) hrun

/-- Endpoint corollary, per flagged component. -/
theorem stratified_barrier_endS (sys : ODESystem (Var n)) (D : Formula (Var n))
    (ts : List (Bool × Term (Var n)))
    (hcert : ∀ i (hi : i < ts.length), ∀ ν', HoldsAt ts[i].1 ts[i].2 ν' →
      ∀ ω, Program.sem (Program.ode sys (Formula.and D (bigLe ((ts.take i).map Prod.snd))))
        ν' ω → HoldsAt ts[i].1 ts[i].2 ω)
    {ν : State (Var n)} (hinit : ∀ c ∈ ts, HoldsAt c.1 c.2 ν) :
    ∀ ω, Program.sem (Program.ode sys D) ν ω → ∀ c ∈ ts, HoldsAt c.1 c.2 ω := by
  intro ω hrun c hc
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hrun
  obtain ⟨i, hi, hic⟩ := List.getElem_of_mem hc
  rw [← hΦr, ← hic]
  exact stratified_barrier_soundS sys D ts hcert hinit hr hΦ0 hder hmask hdom i hi r
    (Set.right_mem_Icc.mpr hr)

/-! ## The Z3 leaf, per stratum, with the strict route groups -/

/-- The flow obligation of stratum `i` of a flagged list: the component, the fields, the
stretch, and the tool's fold-shaped domain over the CLOSURE of the prefix (exactly the
existing query domain: it depends only on the components). -/
def strataObS (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (D : Formula (Var n))
    (ts : List (Bool × Term (Var n))) (i : ℕ) (hi : i < ts.length) : FlowObligation n :=
  ⟨ts[i].2, fL, fR, lam, strataDomHost D ((ts.take i).map Prod.snd)⟩

/-- **The flagged verdict pack.** A strict component is certified by route A or B only;
a non-strict one by any of the three routes (the existing group). -/
def StrataVerdS (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) (D : Formula (Var n))
    (ts : List (Bool × Term (Var n))) : Prop :=
  ∀ i (hi : i < ts.length),
    z3solve (flowQuery (strataObS fL fR lam D ts i hi)) = Verdict.unsat
    ∨ z3solve (flowQueryStrict (strataObS fL fR lam D ts i hi)) = Verdict.unsat
    ∨ (ts[i].1 = false ∧
        z3solve (flowQuerySuperlevel (strataObS fL fR lam D ts i hi)) = Verdict.unsat)

/-- Same-runs transfer between sat-equivalent ode domains, flagged conclusion. -/
theorem holds_dom_congr {sys : ODESystem (Var n)} {D D' : Formula (Var n)}
    (h : ∀ ν, Formula.sat D ν ↔ Formula.sat D' ν) {b : Bool} {g : Term (Var n)}
    {ν : State (Var n)}
    (hbox : ∀ ω, Program.sem (Program.ode sys D') ν ω → HoldsAt b g ω) :
    ∀ ω, Program.sem (Program.ode sys D) ν ω → HoldsAt b g ω := by
  intro ω hsem
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hsem
  exact hbox ω ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => (h (Φ t)).mp (hdom t ht)⟩

/-- **The strata certificates from the flagged verdicts.** Strict strata: routes A/B give
`BoxLt` (`flow_cert_sound_lt`, `flow_cert_sound_strict_lt`); non-strict strata: the existing
three routes give `BoxLe`. -/
theorem strata_hcert_from_verdictsS' (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (D : Formula (Var n)) (ts : List (Bool × Term (Var n)))
    (hz3 : StrataVerdS fL fR lam D ts) :
    ∀ i (hi : i < ts.length), ∀ ν', HoldsAt ts[i].1 ts[i].2 ν' →
      ∀ ω, Program.sem (Program.ode (jointSys fL fR lam)
        (Formula.and D (bigLe ((ts.take i).map Prod.snd)))) ν' ω →
        HoldsAt ts[i].1 ts[i].2 ω := by
  intro i hi ν' hinit
  have hcong : ∀ ν, Formula.sat (Formula.and D (bigLe ((ts.take i).map Prod.snd))) ν ↔
      Formula.sat (strataDomHost D ((ts.take i).map Prod.snd)) ν := by
    intro ν
    rw [sat_strataDomHost]
    constructor
    · rintro ⟨hD, hb⟩
      exact ⟨hD, (sat_bigLe_iff _ _).mp hb⟩
    · rintro ⟨hD, hall⟩
      exact ⟨hD, (sat_bigLe_iff _ _).mpr hall⟩
  refine holds_dom_congr hcong ?_
  have ho : (strataObS fL fR lam D ts i hi).g = ts[i].2 := rfl
  rcases hb : ts[i].1 with _ | _
  · -- non-strict stratum: the existing three routes
    rw [hb] at hinit
    have hinit' : Term.eval (strataObS fL fR lam D ts i hi).g ν' ≤ 0 := hinit
    intro ω hω
    show Term.eval ts[i].2 ω ≤ 0
    rcases hz3 i hi with h | h | ⟨-, h⟩
    · exact flow_cert_sound _ (z3_unsat_sound h) hinit' ω hω
    · exact flow_cert_sound_strict _ (z3_unsat_sound h) hinit' ω hω
    · exact flow_cert_sound_superlevel _ (z3_unsat_sound h) hinit' ω hω
  · -- strict stratum: routes A and B only
    rw [hb] at hinit
    have hinit' : Term.eval (strataObS fL fR lam D ts i hi).g ν' < 0 := hinit
    intro ω hω
    show Term.eval ts[i].2 ω < 0
    rcases hz3 i hi with h | h | ⟨hf, -⟩
    · exact flow_cert_sound_lt _ (z3_unsat_sound h) hinit' ω hω
    · exact flow_cert_sound_strict_lt _ (z3_unsat_sound h) hinit' ω hω
    · rw [hb] at hf; exact absurd hf (by decide)

/-- Multi-component segment preservation, flagged (the strict `SegPreservesAllOn`). -/
def SegPreservesAllOnS (ts : List (Bool × Term (Var n))) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) : Prop :=
  ∀ ν, (∀ c ∈ ts, HoldsAt c.1 c.2 ν) →
    ∀ ω, Program.sem (Program.ode sys dom) ν ω → ∀ c ∈ ts, HoldsAt c.1 c.2 ω

/-- **The flagged multi-component flow certificate, end to end** (fold-shaped domains). -/
theorem segPresAllS_from_strata_verdicts' (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (D : Formula (Var n)) (ts : List (Bool × Term (Var n)))
    (hz3 : StrataVerdS fL fR lam D ts) :
    SegPreservesAllOnS ts (jointSys fL fR lam) D :=
  fun _ hinit => stratified_barrier_endS (jointSys fL fR lam) D ts
    (strata_hcert_from_verdictsS' fL fR lam D ts hz3) hinit

/-! ## Collapse to the existing layer -/

theorem holdsAll_allFalse (gs : List (Term (Var n))) (ν : State (Var n)) :
    (∀ c ∈ gs.map (fun g => (false, g)), HoldsAt c.1 c.2 ν) ↔ ∀ g ∈ gs, Term.eval g ν ≤ 0 := by
  simp [HoldsAt]

/-- With every flag `false`, flagged preservation is the existing preservation. -/
theorem segPresAllOnS_allFalse (gs : List (Term (Var n))) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) :
    SegPreservesAllOnS (gs.map (fun g => (false, g))) sys dom ↔ SegPreservesAllOn gs sys dom := by
  unfold SegPreservesAllOnS SegPreservesAllOn
  simp only [holdsAll_allFalse]

/-- With every flag `false`, the flagged verdict pack is the existing one (the queries are
the same strings: the obligation depends only on the components). -/
theorem strataVerdS_allFalse (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (D : Formula (Var n)) (gs : List (Term (Var n))) :
    StrataVerdS fL fR lam D (gs.map (fun g => (false, g))) ↔
      ∀ i (hi : i < gs.length),
        z3solve (flowQuery ⟨gs[i], fL, fR, lam, strataDomHost D (gs.take i)⟩) = Verdict.unsat
        ∨ z3solve (flowQueryStrict ⟨gs[i], fL, fR, lam,
            strataDomHost D (gs.take i)⟩) = Verdict.unsat
        ∨ z3solve (flowQuerySuperlevel ⟨gs[i], fL, fR, lam,
            strataDomHost D (gs.take i)⟩) = Verdict.unsat := by
  have hmap : (gs.map (fun g => ((false : Bool), g))).map Prod.snd = gs := by
    rw [List.map_map]; exact List.map_id' gs
  constructor
  · intro h i hi
    have hi' : i < (gs.map (fun g => (false, g))).length := by simpa using hi
    have := h i hi'
    simp only [strataObS, List.getElem_map, take_map_snd, hmap] at this
    rcases this with h1 | h1 | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · intro h i hi
    have hi' : i < gs.length := by simpa using hi
    have := h i hi'
    simp only [strataObS, List.getElem_map, take_map_snd, hmap]
    rcases this with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨trivial, h1⟩)

end RelCertifier

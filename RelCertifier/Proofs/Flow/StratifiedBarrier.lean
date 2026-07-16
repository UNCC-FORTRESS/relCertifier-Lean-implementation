/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# R4 — stratified differential cuts, kernel-checked (docs/ROADMAP.md R4)

The tool's `checkSeg` (since commit 1f9b578) certifies invariant components by
STRATIFIED differential cuts: a component's flow query may narrow its domain only by
components proven in EARLIER fixpoint rounds — sequential, acyclic DC. (The previous
mutual narrowing was circular and unsound for the non-strict routes; see
docs/COVER-AUDIT.md R4 and the `x², x' = 1` counterexample.)

This file is the soundness of that discipline, in kernel:

* `sem_ode_restrict` — a run of an ode, cut at any earlier time, is again a run;
* `boxle_pointwise` — a `BoxLe` certificate holds POINTWISE along runs (via restriction);
* `sem_ode_refine` — a run pointwise inside an invariant is a run of the
  invariant-narrowed ode (THE differential-cut step);
* `stratified_barrier_sound` — the induction over strata: if each component carries a
  `BoxLe` certificate over the domain narrowed by its PREFIX (the tool's proven-order),
  then from a jointly-invariant start, every component holds at every reachable state
  of the UN-narrowed ode.

Each stratum's `BoxLe` premise is exactly what the route theorems
(`flow_cert_sound{,_strict,_superlevel}`) produce from the tool's per-stratum queries
(`routeQueries` over `evolve ∧ cuts ∧ bigLe (prefix)`), so the Z3 leaf enters per
component per stratum, nothing else assumed.
-/
import RelCertifier.Core.FlowCert
import RelCertifier.Core.Reify
import RelCertifier.Trusted.Oracle

namespace RelCertifier
open DL Set

variable {n : ℕ}

/-! ## The conjunction formula (the tool's proven-strata narrowing) -/

/-- `bigLe gs` — the conjunction `⋀ g ∈ gs, g ≤ 0` (the strata narrowing). -/
def bigLe (gs : List (Term (Var n))) : Formula (Var n) :=
  gs.foldr (fun g acc => Formula.and (invLe g) acc) Formula.tt

theorem sat_bigLe_iff (gs : List (Term (Var n))) (ν : State (Var n)) :
    Formula.sat (bigLe gs) ν ↔ ∀ g ∈ gs, Term.eval g ν ≤ 0 := by
  induction gs with
  | nil => simp [bigLe, Formula.sat]
  | cons g gs ih =>
      simp only [bigLe, List.foldr_cons, Formula.sat, List.mem_cons] at ih ⊢
      constructor
      · rintro ⟨hg, hrest⟩ g' (rfl | hg')
        · simpa [invLe, Formula.sat, Term.eval, CompOp.interp] using hg
        · exact ih.mp hrest g' hg'
      · intro h
        refine ⟨?_, ih.mpr (fun g' hg' => h g' (Or.inr hg'))⟩
        simpa [invLe, Formula.sat, Term.eval, CompOp.interp] using h g (Or.inl rfl)

/-! ## Run surgery -/

/-- A run of an ode, cut at any earlier time, is again a run (to the cut point). -/
theorem sem_ode_restrict {sys : ODESystem (Var n)} {D : Formula (Var n)}
    {ν : State (Var n)} {r t : ℝ} {Φ : ℝ → State (Var n)}
    (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s)
    (hmask : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ s x = ν x)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ s))
    (ht : t ∈ Set.Icc (0:ℝ) r) :
    Program.sem (Program.ode sys D) ν (Φ t) := by
  refine ⟨t, Φ, ht.1, hΦ0, rfl, ?_, ?_, ?_⟩
  · intro s hs p hp
    exact (hder s ⟨hs.1, hs.2.trans ht.2⟩ p hp).mono (Set.Icc_subset_Icc le_rfl ht.2)
  · intro s hs x hx
    exact hmask s ⟨hs.1, hs.2.trans ht.2⟩ x hx
  · intro s hs
    exact hdom s ⟨hs.1, hs.2.trans ht.2⟩

/-- A `BoxLe` certificate holds POINTWISE along every run (apply it to each cut). -/
theorem boxle_pointwise {sys : ODESystem (Var n)} {D : Formula (Var n)}
    {f : State (Var n) → ℝ} {ν : State (Var n)}
    (hbox : BoxLe (Program.ode sys D) f ν)
    {r : ℝ} {Φ : ℝ → State (Var n)} (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s)
    (hmask : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ s x = ν x)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ s)) :
    ∀ t ∈ Set.Icc (0:ℝ) r, f (Φ t) ≤ 0 := by
  intro t ht
  exact hbox (Φ t) (sem_ode_restrict hr hΦ0 hder hmask hdom ht)

/-- **The differential-cut step.** A run pointwise inside `bigLe gs` is a run of the
`bigLe gs`-narrowed ode — same trajectory, strengthened domain. -/
theorem sem_ode_refine {sys : ODESystem (Var n)} {D : Formula (Var n)}
    (gs : List (Term (Var n))) {ν : State (Var n)}
    {r : ℝ} {Φ : ℝ → State (Var n)} (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s)
    (hmask : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ s x = ν x)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ s))
    (hpt : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gs, Term.eval g (Φ s) ≤ 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) r) :
    Program.sem (Program.ode sys (Formula.and D (bigLe gs))) ν (Φ t) := by
  refine ⟨t, Φ, ht.1, hΦ0, rfl, ?_, ?_, ?_⟩
  · intro s hs p hp
    exact (hder s ⟨hs.1, hs.2.trans ht.2⟩ p hp).mono (Set.Icc_subset_Icc le_rfl ht.2)
  · intro s hs x hx
    exact hmask s ⟨hs.1, hs.2.trans ht.2⟩ x hx
  · intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) r := ⟨hs.1, hs.2.trans ht.2⟩
    exact ⟨hdom s hs', (sat_bigLe_iff gs (Φ s)).mpr (hpt s hs')⟩

/-! ## The stratified assembly -/

/-- **Stratified differential cuts are sound.** If each component `gs[i]` carries a
`BoxLe` certificate over the ode narrowed by its PREFIX `gs.take i` (the tool's
proven-order — round-1 components on the bare domain, later rounds assuming exactly
the earlier strata), then from a jointly-invariant start, EVERY component holds at
every time along every run of the UN-narrowed ode. Induction over strata: the prefix
holds pointwise by the inductive hypothesis, so the run refines into stratum `i`'s
narrowed ode (`sem_ode_refine`), whose certificate then yields `gs[i]` pointwise
(`boxle_pointwise`-style, on each cut). No circularity: the assumption set is always
already proven. -/
theorem stratified_barrier_sound (sys : ODESystem (Var n)) (D : Formula (Var n))
    (gs : List (Term (Var n)))
    (hcert : ∀ i (hi : i < gs.length), ∀ ν', Term.eval gs[i] ν' ≤ 0 →
      BoxLe (Program.ode sys (Formula.and D (bigLe (gs.take i))))
        (fun ω => Term.eval gs[i] ω) ν')
    {ν : State (Var n)} (hinit : ∀ g ∈ gs, Term.eval g ν ≤ 0)
    {r : ℝ} {Φ : ℝ → State (Var n)} (hr : 0 ≤ r) (hΦ0 : Φ 0 = ν)
    (hder : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
      HasDerivWithinAt (fun u => Φ u p.1) (p.2.eval (Φ s)) (Set.Icc 0 r) s)
    (hmask : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ s x = ν x)
    (hdom : ∀ s ∈ Set.Icc (0:ℝ) r, Formula.sat D (Φ s)) :
    ∀ i (hi : i < gs.length), ∀ t ∈ Set.Icc (0:ℝ) r, Term.eval gs[i] (Φ t) ≤ 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi t ht
      -- the prefix holds pointwise (strong IH)
      have hpre : ∀ s ∈ Set.Icc (0:ℝ) r, ∀ g ∈ gs.take i, Term.eval g (Φ s) ≤ 0 := by
        intro s hs g hg
        obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hg
        rw [List.getElem_take] at hjg
        have hjlen : j < gs.length := by
          have := List.length_take_le i gs
          omega
        rw [← hjg]
        exact ih j (by
          have := hj
          rw [List.length_take] at this
          omega) hjlen s hs
      -- refine the run into stratum i's narrowed ode, cut at t
      have hrun := sem_ode_refine (gs.take i) hr hΦ0 hder hmask hdom hpre ht
      -- the stratum certificate fires from the initial state
      have hinit_i : Term.eval gs[i] ν ≤ 0 := hinit _ (List.getElem_mem hi)
      exact hcert i hi ν hinit_i (Φ t) hrun

/-- Endpoint corollary in `BoxLe` shape, per component. -/
theorem stratified_barrier_boxle (sys : ODESystem (Var n)) (D : Formula (Var n))
    (gs : List (Term (Var n)))
    (hcert : ∀ i (hi : i < gs.length), ∀ ν', Term.eval gs[i] ν' ≤ 0 →
      BoxLe (Program.ode sys (Formula.and D (bigLe (gs.take i))))
        (fun ω => Term.eval gs[i] ω) ν')
    {ν : State (Var n)} (hinit : ∀ g ∈ gs, Term.eval g ν ≤ 0) :
    ∀ ω, Program.sem (Program.ode sys D) ν ω → ∀ g ∈ gs, Term.eval g ω ≤ 0 := by
  intro ω hrun g hg
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hrun
  obtain ⟨i, hi, hig⟩ := List.getElem_of_mem hg
  rw [← hΦr, ← hig]
  exact stratified_barrier_sound sys D gs hcert hinit hr hΦ0 hder hmask hdom i hi r
    (Set.right_mem_Icc.mpr hr)

/-! ## The Z3 leaf, per stratum — the tool's exact query discipline -/

/-- Per-stratum route verdicts (the tool's `routeQueries` over the prefix-narrowed
domain, any of the three routes) discharge the strata certificates. -/
theorem strata_hcert_from_verdicts (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (D : Formula (Var n)) (gs : List (Term (Var n)))
    (hz3 : ∀ i (hi : i < gs.length),
      z3solve (flowQuery ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat) :
    ∀ i (hi : i < gs.length), ∀ ν', Term.eval gs[i] ν' ≤ 0 →
      BoxLe (Program.ode (jointSys fL fR lam) (Formula.and D (bigLe (gs.take i))))
        (fun ω => Term.eval gs[i] ω) ν' := by
  intro i hi ν' hinit
  rcases hz3 i hi with h | h | h
  · exact flow_cert_sound _ (z3_unsat_sound h) hinit
  · exact flow_cert_sound_strict _ (z3_unsat_sound h) hinit
  · exact flow_cert_sound_superlevel _ (z3_unsat_sound h) hinit

/-- Multi-component segment preservation (the list form of `SegPreservesOn`). -/
def SegPreservesAllOn (gs : List (Term (Var n))) (sys : ODESystem (Var n))
    (dom : Formula (Var n)) : Prop :=
  ∀ ν, (∀ g ∈ gs, Term.eval g ν ≤ 0) →
    ∀ ω, Program.sem (Program.ode sys dom) ν ω → ∀ g ∈ gs, Term.eval g ω ≤ 0

/-- **The multi-component flow certificate, end to end**: the tool's per-stratum route
verdicts give simultaneous preservation of the FULL component list along the
un-narrowed joint co-evolution. This is the kernel-checked soundness of the stratified
`checkSeg` (commit 1f9b578): the Z3 leaf enters once per component per stratum;
`stratified_barrier_boxle` assembles the acyclic cuts. -/
theorem segPresAll_from_strata_verdicts (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (D : Formula (Var n)) (gs : List (Term (Var n)))
    (hz3 : ∀ i (hi : i < gs.length),
      z3solve (flowQuery ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gs[i], fL, fR, lam,
        Formula.and D (bigLe (gs.take i))⟩) = Verdict.unsat) :
    SegPreservesAllOn gs (jointSys fL fR lam) D :=
  fun _ hinit => stratified_barrier_boxle (jointSys fL fR lam) D gs
    (strata_hcert_from_verdicts fL fR lam D gs hz3) hinit

/-! ## The fold-shaped domains (the tool's exact `strataDomIR` image) -/

/-- The host image of `strataDomIR`: base narrowed by a left fold of `≤ 0` conjuncts —
the EXACT formula shape of the tool's stratified queries. -/
def strataDomHost (D : Formula (Var n)) (pre : List (Term (Var n))) : Formula (Var n) :=
  pre.foldl (fun d g => Formula.and d (invLe g)) D

theorem sat_strataDomHost (D : Formula (Var n)) (pre : List (Term (Var n)))
    (ν : State (Var n)) :
    Formula.sat (strataDomHost D pre) ν ↔
      Formula.sat D ν ∧ ∀ g ∈ pre, Term.eval g ν ≤ 0 := by
  induction pre generalizing D with
  | nil => simp [strataDomHost]
  | cons g pre ih =>
      simp only [strataDomHost, List.foldl_cons] at ih ⊢
      rw [ih (Formula.and D (invLe g))]
      constructor
      · rintro ⟨⟨hD, hg⟩, hrest⟩
        refine ⟨hD, ?_⟩
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa [invLe, Formula.sat, Term.eval, CompOp.interp] using hg
        · exact hrest g' hg'
      · rintro ⟨hD, hall⟩
        have hg0 : Term.eval g ν ≤ 0 := hall g List.mem_cons_self
        exact ⟨⟨hD, by simpa [invLe, Formula.sat, Term.eval, CompOp.interp] using hg0⟩,
          fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')⟩

/-- Same-runs transfer between sat-equivalent ode domains. -/
theorem boxle_dom_congr {sys : ODESystem (Var n)} {D D' : Formula (Var n)}
    (h : ∀ ν, Formula.sat D ν ↔ Formula.sat D' ν) {f : State (Var n) → ℝ}
    {ν : State (Var n)} (hbox : BoxLe (Program.ode sys D') f ν) :
    BoxLe (Program.ode sys D) f ν := by
  intro ω hsem
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hsem
  exact hbox ω ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, fun t ht => (h (Φ t)).mp (hdom t ht)⟩

/-- **The Z3 leaf, fold-shaped** — verdicts on the tool's EXACT stratified query domains
(`strataDomHost`, the host image of `strataDomIR`) discharge the strata certificates in
the `bigLe` shape `stratified_barrier_sound` consumes. -/
theorem strata_hcert_from_verdicts' (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (D : Formula (Var n)) (gs : List (Term (Var n)))
    (hz3 : ∀ i (hi : i < gs.length),
      z3solve (flowQuery ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat) :
    ∀ i (hi : i < gs.length), ∀ ν', Term.eval gs[i] ν' ≤ 0 →
      BoxLe (Program.ode (jointSys fL fR lam) (Formula.and D (bigLe (gs.take i))))
        (fun ω => Term.eval gs[i] ω) ν' := by
  intro i hi ν' hinit
  have hcong : ∀ ν, Formula.sat (Formula.and D (bigLe (gs.take i))) ν ↔
      Formula.sat (strataDomHost D (gs.take i)) ν := by
    intro ν
    rw [sat_strataDomHost]
    constructor
    · rintro ⟨hD, hb⟩
      exact ⟨hD, (sat_bigLe_iff _ _).mp hb⟩
    · rintro ⟨hD, hall⟩
      exact ⟨hD, (sat_bigLe_iff _ _).mpr hall⟩
  refine boxle_dom_congr hcong ?_
  rcases hz3 i hi with h | h | h
  · exact flow_cert_sound _ (z3_unsat_sound h) hinit
  · exact flow_cert_sound_strict _ (z3_unsat_sound h) hinit
  · exact flow_cert_sound_superlevel _ (z3_unsat_sound h) hinit

/-- Fold-shaped end-to-end multi-component certificate (the battery entry point). -/
theorem segPresAll_from_strata_verdicts' (fL fR : Fin n → Term (Var n))
    (lam : Term (Var n)) (D : Formula (Var n)) (gs : List (Term (Var n)))
    (hz3 : ∀ i (hi : i < gs.length),
      z3solve (flowQuery ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQueryStrict ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat
      ∨ z3solve (flowQuerySuperlevel ⟨gs[i], fL, fR, lam,
        strataDomHost D (gs.take i)⟩) = Verdict.unsat) :
    SegPreservesAllOn gs (jointSys fL fR lam) D :=
  fun _ hinit => stratified_barrier_boxle (jointSys fL fR lam) D gs
    (strata_hcert_from_verdicts' fL fR lam D gs hz3) hinit

end RelCertifier

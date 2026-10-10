/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Assumption 1 (Well-Formedness) of the right model, as a predicate (`WellFormedR`)

The paper's Assumption 1, as restated 2026-10-10: *the right model is nonblocking and
complete with respect to its declared successor relation: from every state satisfying a
source-mode guard, an evolution spanning the control interval `ε_r` exists, and every
evolution of duration at most `ε_r`, including the empty one, ends in a state satisfying
the guard of at least one declared successor mode.*

`WellFormedR G guard ε` states it for a right graph `G` (the instances' guarded right
automaton: modes are the file's lowered flows over its evolve domain, edges are the
file's `next` lists), the lowered right guards `guard q`, and `ε = ε_r` read from the file
(`epsR`, the tool's own reading of `epsilon`). For every mode `q` and every state `x` in
`q`'s guard and `q`'s evolve domain:

* (i) **nonblocking**: some run of `q`'s flow of duration exactly `ε` exists inside the
  evolve domain;
* (ii) **successor-completeness**: every run of `q`'s flow of duration `t ≤ ε` (inside
  the domain, `t = 0` included) ends where the lowered guard of some declared successor
  `e.tgt`, `e ∈ G.edgesFrom q`, holds (the self-loop counts).

**The evolve-domain conjunct.** The states of the automaton are the states of its evolve
domain: a run (even the empty one) exists only from a state of the domain (`ODESol.hdom`
at time 0, `ODESol.start_dom`). Without that conjunct clause (i) would be false at every
guard state outside the domain (e.g. `watertank`'s `PumpOff` guard `x < 2` admits `x = −1`,
outside `0 ≤ x ≤ 25`) for a reason that has nothing to do with the model's dynamics. The
retired settling checker made the same correction (`Checker/WellFormedChecker.lean`, "THE
BASE-SET CORRECTION": its guard map is `envelope ∧ guard-band`). Theorem 3's invariant
carries the evolve domain too (`domR` in `envLR`).

**Region-relative form.** `WellFormedRIn G guard reg ε` quantifies only over states in
`reg` as well; `WellFormedR` is the form with `reg = ⊤`. It is used where (i) holds only on
a conserved-quantity band of the model (the six satellite benchmarks), and is then stated
together with `RegionInvariant G reg` (every mode's flow keeps `reg`; jumps do not move
the state), so the band is a property of the model's reachable states.

The predicate is a MODEL fact: it mentions neither the relational invariant nor the left
system. It is not a hypothesis of any Theorem 3 (those exhibit their responses
explicitly); it is an additional, separately audited result (`InstancesV2/WellFormed/`,
`WellFormedBattery`).

Generic support below: the per-mode and whole-graph forms, a refutation lemma (one
explicit run that ends outside every successor guard), and the run lemmas the
per-benchmark proofs use (closed form of a linear coordinate, rate bounds, frozen
coordinates, existence from `WellFormedFlowB`).

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.Proofs.Flow.DISuperlevel
import RelCertifier.Proofs.Encoding.RightOnlyStay
import RelCertifier.Proofs.Encoding.Reparam
import RelCertifier.Trusted.Run

namespace RelCertifier
open DL DLCalTiming Set

variable {n : ℕ}

/-! ## The predicate -/

/-- `ε_r` as the tool reads it (`OracleAPI.certifyWithData`: `(parseRat p.R.epsilon).getD 1`). -/
noncomputable def epsR (p : Parse.PProblem) : ℝ :=
  (((Run.parseRat p.R.epsilon).getD 1 : ℚ) : ℝ)

/-- **Assumption 1 at right mode `q`**, on the states of `reg`: from every state of `q`'s
guard and evolve domain (and `reg`), (i) a run of `q`'s flow of duration `ε` exists, and
(ii) every run of duration `t ≤ ε` ends in the guard of a declared successor of `q`. -/
def WellFormedRModeIn (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (reg : Formula (Var n)) (ε : ℝ) (q : ℕ) : Prop :=
  ∀ m, G.modeAt q = some m →
    ∀ x, Formula.sat (guard q) x → Formula.sat m.dom x → Formula.sat reg x →
      (∃ Φ, ODESol m.sys m.dom x ε Φ) ∧
      ∀ (t : ℝ) (Φ : ℝ → State (Var n)), t ≤ ε → ODESol m.sys m.dom x t Φ →
        ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t)

/-- Assumption 1 for every mode of `G`, on the states of `reg`. -/
def WellFormedRIn (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (reg : Formula (Var n)) (ε : ℝ) : Prop :=
  ∀ q, q < G.modes.length → WellFormedRModeIn G guard reg ε q

/-- Assumption 1 at one mode, on all states (of the guard and the evolve domain). -/
def WellFormedRMode (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n)) (ε : ℝ)
    (q : ℕ) : Prop :=
  WellFormedRModeIn G guard Formula.tt ε q

/-- **Assumption 1 (Well-Formedness) of the right model `G`**, guards `guard`, control
interval `ε`: for every mode `q` and every state `x` in `q`'s guard and evolve domain,
(i) a run of `q`'s flow of duration `ε` exists inside the domain, and (ii) every run of
duration `t ≤ ε` from `x` ends in the guard of some declared successor of `q`. -/
def WellFormedR (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n)) (ε : ℝ) : Prop :=
  WellFormedRIn G guard Formula.tt ε

/-- The region `reg` is kept by every mode's flow (a jump does not move the state, so
`reg` then holds at every reachable state of the right model that starts in it). -/
def RegionInvariant (G : SearchGraph (Var n)) (reg : Formula (Var n)) : Prop :=
  ∀ q m, G.modeAt q = some m → ∀ (x : State (Var n)) (t : ℝ) (Φ : ℝ → State (Var n)),
    Formula.sat reg x → ODESol m.sys m.dom x t Φ → Formula.sat reg (Φ t)

theorem wellFormedR_iff_modes (G : SearchGraph (Var n)) (guard : ℕ → Formula (Var n))
    (ε : ℝ) : WellFormedR G guard ε ↔ ∀ q, q < G.modes.length → WellFormedRMode G guard ε q :=
  Iff.rfl

/-- The `⊤`-region form is the region form at any region. -/
theorem WellFormedRIn.of_tt {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)} {ε : ℝ}
    (h : WellFormedR G guard ε) (reg : Formula (Var n)) : WellFormedRIn G guard reg ε :=
  fun q hq m hm x hg hd _ => h q hq m hm x hg hd trivial

/-- A per-mode proof needs only the states, not the trivial region membership. -/
theorem wellFormedRMode_intro {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {ε : ℝ} {q : ℕ}
    (h : ∀ m, G.modeAt q = some m → ∀ x, Formula.sat (guard q) x → Formula.sat m.dom x →
      (∃ Φ, ODESol m.sys m.dom x ε Φ) ∧
      ∀ (t : ℝ) (Φ : ℝ → State (Var n)), t ≤ ε → ODESol m.sys m.dom x t Φ →
        ∃ e ∈ G.edgesFrom q, Formula.sat (guard e.tgt) (Φ t)) :
    WellFormedRMode G guard ε q :=
  fun m hm x hg hd _ => h m hm x hg hd

/-- With the edges carrying the entered mode's guard (`Gr_guards`), clause (ii) is a legal
switch: the edge it picks passes its own test. -/
theorem wellFormedR_switchLegal {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    (hG : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = guard e.tgt) {q : ℕ} {e : REdge (Var n)}
    (he : e ∈ G.edgesFrom q) {μ : State (Var n)} (h : Formula.sat (guard e.tgt) μ) :
    SwitchLegal e μ := by
  unfold SwitchLegal; rw [hG q e he]; exact h

/-! ## Runs: elementary facts -/

/-- A run starts in its domain (the reason the predicate quantifies over domain states). -/
theorem _root_.DLCalTiming.ODESol.start_dom {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ) :
    Formula.sat dom x := by
  have h := H.hdom 0 ⟨le_refl 0, H.hr⟩
  rwa [H.hΦ0] at h

/-- A run ends in its domain. -/
theorem _root_.DLCalTiming.ODESol.end_dom {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ) :
    Formula.sat dom (Φ r) :=
  H.hdom r ⟨H.hr, le_refl r⟩

/-- The run as a program transition `x → Φ r`. -/
theorem _root_.DLCalTiming.ODESol.sem {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ) :
    Program.sem (Program.ode sys dom) x (Φ r) :=
  DLCalTiming.sem_ode_restrict H H.hr (le_refl r)

/-- A coordinate the system does not bind is frozen along the run. -/
theorem _root_.DLCalTiming.ODESol.frozen {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} (hy : y ∉ sys.bound) : Φ r y = x y :=
  H.hmask r ⟨H.hr, le_refl r⟩ y hy

/-- **Closed form of a linear coordinate** along a run, at its end: `y' = k (c − y)` on the
domain gives `y(r) = c + (y₀ − c) e^{−k r'}` for some `r' ≥ 0` (`ode_linear_coord`). -/
theorem _root_.DLCalTiming.ODESol.linear {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) :
    ∃ r', 0 ≤ r' ∧ Φ r y = c + (x y - c) * Real.exp (-(k * r')) :=
  ode_linear_coord H.sem hy k c hf

/-- **Closed form of a linear coordinate, at the run's own duration**: `y' = k (c − y)` on
the domain gives `y(r) = c + (y₀ − c) e^{−k r}` for the run's duration `r`. -/
theorem _root_.DLCalTiming.ODESol.linear_exact {sys : ODESystem (Var n)}
    {dom : Formula (Var n)} {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys dom x r Φ) {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) :
    Φ r y = c + (x y - c) * Real.exp (-(k * r)) := by
  set G : ℝ → ℝ := fun t => (c - Φ t y) * Real.exp (k * t) with hG
  have hGder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt G 0 (Set.Icc 0 r) t := by
    intro t ht
    have h1 := H.hder t ht (y, f) hy
    rw [hf _ (H.hdom t ht)] at h1
    have h2 : HasDerivWithinAt (fun u => Real.exp (k * u)) (Real.exp (k * t) * (k * 1))
        (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul k).exp).hasDerivWithinAt
    exact ((h1.const_sub c).mul h2).congr_deriv (by ring)
  have hcont : ContinuousOn G (Set.Icc 0 r) := fun t ht => (hGder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hGder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨H.hr, le_refl r⟩
  simp only [hG, H.hΦ0, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (k * r) * Real.exp (-(k * r)) = 1 := by
    rw [← Real.exp_add]; simp
  have : c - Φ r y = (c - x y) * Real.exp (-(k * r)) := by
    calc c - Φ r y = (c - Φ r y) * (Real.exp (k * r) * Real.exp (-(k * r))) := by
          rw [hexp, mul_one]
      _ = ((c - Φ r y) * Real.exp (k * r)) * Real.exp (-(k * r)) := by ring
      _ = (c - x y) * Real.exp (-(k * r)) := by rw [hconst]
  linarith

/-- A linear coordinate stays between its start and its set point (`k ≥ 0`). -/
theorem _root_.DLCalTiming.ODESol.linear_between {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ) (hk : 0 ≤ k)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) :
    min (x y) c ≤ Φ r y ∧ Φ r y ≤ max (x y) c := by
  obtain ⟨r', hr', heq⟩ := H.linear hy k c hf
  have he0 : 0 < Real.exp (-(k * r')) := Real.exp_pos _
  have he1 : Real.exp (-(k * r')) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  rw [heq]
  rcases le_total (x y) c with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor <;> nlinarith
  · rw [min_eq_right h, max_eq_left h]
    constructor <;> nlinarith

/-- A linear coordinate below its set point rises toward it (`k ≥ 0`). -/
theorem _root_.DLCalTiming.ODESol.linear_up {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ) (hk : 0 ≤ k)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) (hle : x y ≤ c) :
    x y ≤ Φ r y ∧ Φ r y ≤ c := by
  have h := H.linear_between hy k c hk hf
  rwa [min_eq_left hle, max_eq_right hle] at h

/-- A linear coordinate above its set point falls toward it (`k ≥ 0`). -/
theorem _root_.DLCalTiming.ODESol.linear_down {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ) (hk : 0 ≤ k)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) (hle : c ≤ x y) :
    c ≤ Φ r y ∧ Φ r y ≤ x y := by
  have h := H.linear_between hy k c hk hf
  rwa [min_eq_right hle, max_eq_left hle] at h

/-- A linear coordinate that starts strictly below (above) its set point stays strictly
below (above) it. -/
theorem _root_.DLCalTiming.ODESol.linear_lt {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) (hlt : x y < c) :
    Φ r y < c := by
  obtain ⟨r', -, heq⟩ := H.linear hy k c hf
  have he0 : 0 < Real.exp (-(k * r')) := Real.exp_pos _
  rw [heq]; nlinarith

theorem _root_.DLCalTiming.ODESol.linear_gt {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k c : ℝ)
    (hf : ∀ s, Formula.sat dom s → Term.eval f s = k * (c - s y)) (hgt : c < x y) :
    c < Φ r y := by
  obtain ⟨r', -, heq⟩ := H.linear hy k c hf
  have he0 : 0 < Real.exp (-(k * r')) := Real.exp_pos _
  rw [heq]; nlinarith

/-- **Rate bound from above**: a coordinate whose field is at most `B` along the run grows
by at most `B r` over a run of duration `r`. -/
theorem _root_.DLCalTiming.ODESol.rate_le {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (B : ℝ)
    (hB : ∀ s, Formula.sat dom s → Term.eval f s ≤ B) : Φ r y ≤ x y + B * r := by
  set g : ℝ → ℝ := fun u => B * u - Φ u y with hg
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt g (B - Term.eval f (Φ t)) (Set.Icc 0 r) t := by
    intro t ht
    have h1 := H.hder t ht (y, f) hy
    have h2 : HasDerivWithinAt (fun u : ℝ => B * u) B (Set.Icc 0 r) t := by
      simpa using ((hasDerivAt_id t).const_mul B).hasDerivWithinAt
    exact h2.sub h1
  have hcont : ContinuousOn g (Set.Icc 0 r) := fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn g (Set.Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hB _ (H.hdom t (Set.Ioo_subset_Icc_self ht))
      linarith
  have := hmono ⟨le_refl 0, H.hr⟩ ⟨H.hr, le_refl r⟩ H.hr
  simp only [hg, mul_zero, zero_sub, H.hΦ0] at this
  linarith

/-- **Rate bound from below.** -/
theorem _root_.DLCalTiming.ODESol.rate_ge {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (B : ℝ)
    (hB : ∀ s, Formula.sat dom s → B ≤ Term.eval f s) : x y + B * r ≤ Φ r y := by
  set g : ℝ → ℝ := fun u => Φ u y - B * u with hg
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt g (Term.eval f (Φ t) - B) (Set.Icc 0 r) t := by
    intro t ht
    have h1 := H.hder t ht (y, f) hy
    have h2 : HasDerivWithinAt (fun u : ℝ => B * u) B (Set.Icc 0 r) t := by
      simpa using ((hasDerivAt_id t).const_mul B).hasDerivWithinAt
    exact h1.sub h2
  have hcont : ContinuousOn g (Set.Icc 0 r) := fun t ht => (hderiv t ht).continuousWithinAt
  have hmono : MonotoneOn g (Set.Icc 0 r) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact ((hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at ht
      rw [((hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have := hB _ (H.hdom t (Set.Ioo_subset_Icc_self ht))
      linarith
  have := hmono ⟨le_refl 0, H.hr⟩ ⟨H.hr, le_refl r⟩ H.hr
  simp only [hg, mul_zero, sub_zero, H.hΦ0] at this
  linarith

/-- A coordinate with a nonnegative field does not decrease along the run. -/
theorem _root_.DLCalTiming.ODESol.mono {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys)
    (hB : ∀ s, Formula.sat dom s → 0 ≤ Term.eval f s) : x y ≤ Φ r y := by
  have := H.rate_ge hy 0 hB
  linarith

/-- A coordinate whose field vanishes on the domain is constant along the run. -/
theorem _root_.DLCalTiming.ODESol.const {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys)
    (h0 : ∀ s, Formula.sat dom s → Term.eval f s = 0) : Φ r y = x y := by
  have h1 := H.rate_le hy 0 (fun s hs => (h0 s hs).le)
  have h2 := H.rate_ge hy 0 (fun s hs => (h0 s hs).ge)
  linarith

/-- The restriction of a run to `[0, s]` is a run of duration `s`. -/
theorem _root_.DLCalTiming.ODESol.restrict {sys : ODESystem (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys dom x r Φ)
    {s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : ODESol sys dom x s Φ := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 r := fun u hu => ⟨hu.1, hu.2.trans hsr⟩
  exact ⟨hs, H.hΦ0, fun t ht p hp => (H.hder t (hsub ht) p hp).mono hsub,
    fun t ht y hy => H.hmask t (hsub ht) y hy, fun t ht => H.hdom t (hsub ht)⟩

/-- **A conserved affine combination of two coordinates**: if `a f₁ + b f₂ = 0` on the
domain, `a y₁ + b y₂` is constant along the run. -/
theorem _root_.DLCalTiming.ODESol.affine_const {sys : ODESystem (Var n)}
    {dom : Formula (Var n)} {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys dom x r Φ) {y₁ y₂ : Var n} {f₁ f₂ : Term (Var n)}
    (h₁ : (y₁, f₁) ∈ sys) (h₂ : (y₂, f₂) ∈ sys) (a b : ℝ)
    (h0 : ∀ s, Formula.sat dom s → a * Term.eval f₁ s + b * Term.eval f₂ s = 0) :
    a * Φ r y₁ + b * Φ r y₂ = a * x y₁ + b * x y₂ := by
  set G : ℝ → ℝ := fun t => a * Φ t y₁ + b * Φ t y₂ with hG
  have hGder : ∀ t ∈ Set.Icc (0:ℝ) r, HasDerivWithinAt G 0 (Set.Icc 0 r) t := by
    intro t ht
    have d1 := (H.hder t ht (y₁, f₁) h₁).const_mul a
    have d2 := (H.hder t ht (y₂, f₂) h₂).const_mul b
    exact (d1.add d2).congr_deriv (h0 _ (H.hdom t ht))
  have hcont : ContinuousOn G (Set.Icc 0 r) := fun t ht => (hGder t ht).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht =>
    (hGder t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    r ⟨H.hr, le_refl r⟩
  simp only [hG, H.hΦ0] at hconst
  exact hconst

/-- A coordinate with field `−k y` (`k ≥ 0`) does not grow in magnitude. -/
theorem _root_.DLCalTiming.ODESol.decay_sq_le {sys : ODESystem (Var n)}
    {dom : Formula (Var n)} {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys dom x r Φ) {y : Var n} {f : Term (Var n)} (hy : (y, f) ∈ sys) (k : ℝ)
    (hk : 0 ≤ k) (hf : ∀ s, Formula.sat dom s → Term.eval f s = -k * s y) :
    Φ r y * Φ r y ≤ x y * x y := by
  have hb := H.linear_between hy k 0 hk (fun s hs => by rw [hf s hs]; ring)
  rcases le_total (x y) 0 with h | h
  · rw [min_eq_left h, max_eq_right h] at hb; nlinarith [hb.1, hb.2]
  · rw [min_eq_right h, max_eq_left h] at hb; nlinarith [hb.1, hb.2]

/-! ## The right block -/

theorem rightBlock_mem' (fR : Fin n → Term (Var n)) (lam : Term (Var n)) (i : Fin n) :
    (Rv i, Term.binop .mul lam (fR i)) ∈ rightBlock fR lam :=
  List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- The right block at unit stretch evaluates to the field. -/
theorem eval_unit_mul (f : Term (Var n)) (s : State (Var n)) :
    Term.eval (Term.binop .mul (Term.const 1) f) s = Term.eval f s := by
  simp [Term.eval, AOp.interp]

/-- **Existence (clause (i)) from the instances' `WellFormedFlowB`** at unit stretch. -/
theorem exists_of_wellFormedFlowB {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    {ε : ℝ} (hε : 0 ≤ ε) (hwf : WellFormedFlowB fR (Term.const 1) domR ε)
    {x : State (Var n)} (hx : Formula.sat domR x) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x ε Φ := by
  obtain ⟨Φ, h0, hder, hmask, hdom⟩ := hwf x hx ε hε le_rfl
  exact ⟨Φ, ⟨hε, h0, hder, hmask, hdom⟩⟩

/-! ## Barriers on one right coordinate (nonlinear fields) -/

theorem odeField_rightBlock_unit (fR : Fin n → Term (Var n)) (x : State (Var n)) (j : Fin n) :
    odeField (rightBlock fR (Term.const 1)) x (Rv j) = Term.eval (fR j) x := by
  have hmem := rightBlock_mem' fR (Term.const 1) j
  have hb : Rv j ∈ (rightBlock fR (Term.const 1)).bound :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  simp only [odeField, if_pos hb,
    ODESystem.rhs_eq_of_mem (rightBlock_wellFormed fR (Term.const 1)) hmem]
  exact eval_unit_mul (fR j) x

/-- **Upper barrier**: if the field of `x_j` is nonpositive wherever `x_j ≥ K` (in the
domain), a run from `x_j ≤ K` stays at `x_j ≤ K` (`DI_nonstrict_superlevel`). -/
theorem _root_.DLCalTiming.ODESol.coord_le_barrier {fR : Fin n → Term (Var n)}
    {dom : Formula (Var n)} {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x r Φ) (j : Fin n) (K : ℝ)
    (hb : ∀ s, Formula.sat dom s → K ≤ s (Rv j) → Term.eval (fR j) s ≤ 0)
    (h0 : x (Rv j) ≤ K) : Φ r (Rv j) ≤ K := by
  have hbox := DI_nonstrict_superlevel (sys := rightBlock fR (Term.const 1)) (ψ := dom)
    (g := fun y => (1:ℝ) * y (Rv j) + (-K)) (rightBlock_wellFormed fR (Term.const 1))
    (((differentiable_apply (Rv j)).const_mul 1).add_const (-K))
    (fun y hy hge => by
      rw [lie_affine_coord _ (rightBlock_wellFormed fR (Term.const 1)) (Rv j) 1 (-K) y,
        odeField_rightBlock_unit]
      have := hb y hy (by linarith)
      linarith)
    (ν := x) (by linarith)
  have := hbox (Φ r) H.sem
  simp only at this
  linarith

/-- **Lower barrier**: if the field of `x_j` is nonnegative wherever `x_j ≤ K` (in the
domain), a run from `x_j ≥ K` stays at `x_j ≥ K`. -/
theorem _root_.DLCalTiming.ODESol.coord_ge_barrier {fR : Fin n → Term (Var n)}
    {dom : Formula (Var n)} {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x r Φ) (j : Fin n) (K : ℝ)
    (hb : ∀ s, Formula.sat dom s → s (Rv j) ≤ K → 0 ≤ Term.eval (fR j) s)
    (h0 : K ≤ x (Rv j)) : K ≤ Φ r (Rv j) := by
  have hbox := DI_nonstrict_superlevel (sys := rightBlock fR (Term.const 1)) (ψ := dom)
    (g := fun y => (-1:ℝ) * y (Rv j) + K) (rightBlock_wellFormed fR (Term.const 1))
    (((differentiable_apply (Rv j)).const_mul (-1)).add_const K)
    (fun y hy hge => by
      rw [lie_affine_coord _ (rightBlock_wellFormed fR (Term.const 1)) (Rv j) (-1) K y,
        odeField_rightBlock_unit]
      have := hb y hy (by linarith)
      linarith)
    (ν := x) (by linarith)
  have := hbox (Φ r) H.sem
  simp only at this
  linarith

/-! ## Time reparametrization and existence through a zero-left segment -/

/-- **Time reparametrization of a run** (`sem_rightBlock_reparam` with the duration kept):
a run of the `c`-stretched right block of duration `r` is a run of the `d`-stretched one of
duration `r c / d`. -/
theorem _root_.DLCalTiming.ODESol.reparam {fR : Fin n → Term (Var n)} {dom : Formula (Var n)}
    {x : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)} (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (H : ODESol (rightBlock fR (Term.const c)) dom x r Φ) :
    ODESol (rightBlock fR (Term.const d)) dom x (r * c / d) (fun u => Φ (d * u / c)) := by
  have hscale : ∀ u, 0 ≤ u → u ≤ r * c / d → d * u / c ∈ Set.Icc (0:ℝ) r := by
    intro u hu0 hu2
    constructor
    · positivity
    · rw [div_le_iff₀ hc]
      have h2 : d * u ≤ d * (r * c / d) := mul_le_mul_of_nonneg_left hu2 hd.le
      have h3 : d * (r * c / d) = r * c := by field_simp
      linarith
  have hr := H.hr
  refine ⟨by positivity, by simp [H.hΦ0], ?_, ?_, ?_⟩
  · intro u hu p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    have hmem := rightBlock_mem' fR (Term.const c) i
    have hΦder := H.hder (d * u / c) (hscale u hu.1 hu.2) _ hmem
    have hσ : HasDerivWithinAt (fun v : ℝ => d * v / c) (d / c)
        (Set.Icc 0 (r * c / d)) u := by
      have hda : HasDerivAt (fun v : ℝ => d * v / c) (d / c) u := by
        simpa using ((hasDerivAt_id u).const_mul d).div_const c
      exact hda.hasDerivWithinAt
    have hmaps : Set.MapsTo (fun v : ℝ => d * v / c) (Set.Icc 0 (r * c / d))
        (Set.Icc 0 r) := fun v hv => hscale v hv.1 hv.2
    have hcomp := HasDerivWithinAt.scomp u hΦder hσ hmaps
    have hval : Term.eval (Term.binop AOp.mul (Term.const d) (fR i)) (Φ (d * u / c))
        = (d / c) * Term.eval (Term.binop AOp.mul (Term.const c) (fR i))
            (Φ (d * u / c)) := by
      simp only [Term.eval, AOp.interp]
      field_simp
    show HasDerivWithinAt (fun v => Φ (d * v / c) (Rv i)) _ _ u
    rw [hval]
    have hfun : (fun v => Φ (d * v / c) (Rv i))
        = (fun s => Φ s (Rv i)) ∘ fun v => d * v / c := rfl
    rw [hfun]
    exact hcomp
  · intro u hu y hy
    refine H.hmask (d * u / c) (hscale u hu.1 hu.2) y ?_
    intro hb
    refine hy ?_
    simp only [ODESystem.bound, rightBlock, List.map_map, List.mem_map] at hb ⊢
    obtain ⟨i, hi, hie⟩ := hb
    exact ⟨i, hi, hie⟩
  · intro u hu
    exact H.hdom (d * u / c) (hscale u hu.1 hu.2)

/-- **Existence (clause (i)) from a segment-existence fact with a ZERO left field** at stretch
`λ > 0` (the instances' viability route, `HExistSegB_of_viability_stratified`, instantiated
with `fL = 0`, the left held still): a right run of duration `s λ` at unit stretch. -/
theorem exists_of_HExistSegB_zero {fR : Fin n → Term (Var n)} {lam : ℝ} (hlam : 0 < lam)
    {domR : Formula (Var n)} {dt : ℝ} {ν : State (Var n)}
    (h : HExistSegB (fun _ => Term.const 0) fR (Term.const lam) Formula.tt domR dt ν)
    {s : ℝ} (hs : 0 ≤ s) (hsdt : s ≤ dt) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR ν (s * lam) Φ := by
  obtain ⟨ΦR, h0, hder, hmask, hdom⟩ := h s (fun _ => ν) hs hsdt rfl
    (by
      intro t _ p hp
      simp only [leftBlock, List.mem_map, List.mem_finRange, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hasDerivWithinAt_const _ _ _)
    (fun _ _ _ _ => rfl) (fun _ _ => trivial)
  have H : ODESol (rightBlock fR (Term.const lam)) domR ν s ΦR := ⟨hs, h0, hder, hmask, hdom⟩
  have H' := H.reparam lam 1 hlam one_pos
  rw [div_one] at H'
  exact ⟨_, H'⟩

/-- **The frozen run**: a right block whose every field vanishes holds the state still. -/
theorem const_sol {fR : Fin n → Term (Var n)} {dom : Formula (Var n)}
    (h0 : ∀ i s, Term.eval (fR i) s = 0) {x : State (Var n)} (hx : Formula.sat dom x)
    {r : ℝ} (hr : 0 ≤ r) : ODESol (rightBlock fR (Term.const 1)) dom x r (fun _ => x) := by
  refine ⟨hr, rfl, ?_, fun _ _ _ _ => rfl, fun _ _ => hx⟩
  intro t _ p hp
  simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
  obtain ⟨i, rfl⟩ := hp
  rw [eval_unit_mul, h0]
  exact hasDerivWithinAt_const _ _ _

/-! ## One-coordinate trajectories (explicit runs) -/

/-- The trajectory that moves only the right coordinate `j` along `φ`, every other variable
frozen at `x`. -/
noncomputable def trajJ (x : State (Var n)) (j : Fin n) (φ : ℝ → ℝ) (t : ℝ) : State (Var n) :=
  fun y => if y = Rv j then φ t else x y

@[simp] theorem trajJ_j (x : State (Var n)) (j : Fin n) (φ : ℝ → ℝ) (t : ℝ) :
    trajJ x j φ t (Rv j) = φ t := by simp [trajJ]

theorem trajJ_ne (x : State (Var n)) (j : Fin n) (φ : ℝ → ℝ) (t : ℝ) {y : Var n}
    (hy : y ≠ Rv j) : trajJ x j φ t y = x y := by simp [trajJ, hy]

theorem trajJ_Rv_ne (x : State (Var n)) (j : Fin n) (φ : ℝ → ℝ) (t : ℝ) {i : Fin n}
    (hi : i ≠ j) : trajJ x j φ t (Rv i) = x (Rv i) :=
  trajJ_ne x j φ t (fun h => hi (by simpa [Rv, Prod.ext_iff] using h))

/-- **An explicit one-coordinate run** of the right block at unit stretch: `φ` starts at
`x_j` and has the field's derivative, every other right field vanishes along it, and the
domain holds along it. -/
theorem trajJ_sol {fR : Fin n → Term (Var n)} {domR : Formula (Var n)} (x : State (Var n))
    (j : Fin n) (φ : ℝ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (h0 : φ 0 = x (Rv j))
    (hder : ∀ t, 0 ≤ t → t ≤ ε → HasDerivAt φ (Term.eval (fR j) (trajJ x j φ t)) t)
    (hzero : ∀ i, i ≠ j → ∀ t, 0 ≤ t → t ≤ ε → Term.eval (fR i) (trajJ x j φ t) = 0)
    (hdom : ∀ t, 0 ≤ t → t ≤ ε → Formula.sat domR (trajJ x j φ t)) :
    ODESol (rightBlock fR (Term.const 1)) domR x ε (trajJ x j φ) := by
  refine ⟨hε, ?_, ?_, ?_, fun t ht => hdom t ht.1 ht.2⟩
  · funext y
    by_cases hy : y = Rv j
    · subst hy; simp [h0]
    · exact trajJ_ne x j φ 0 hy
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    show HasDerivWithinAt (fun u => trajJ x j φ u (Rv i))
      (Term.eval (Term.binop .mul (Term.const 1) (fR i)) (trajJ x j φ t)) (Icc 0 ε) t
    rw [eval_unit_mul]
    by_cases hij : i = j
    · subst hij
      have hf : (fun u => trajJ x i φ u (Rv i)) = φ := by funext u; simp
      rw [hf]
      exact (hder t ht.1 ht.2).hasDerivWithinAt
    · have hf : (fun u => trajJ x j φ u (Rv i)) = fun _ => x (Rv i) := by
        funext u; exact trajJ_Rv_ne x j φ u hij
      rw [hf, hzero i hij t ht.1 ht.2]
      exact hasDerivWithinAt_const _ _ _
  · intro t _ y hy
    refine trajJ_ne x j φ t (fun h => hy ?_)
    subst h
    simp only [rightBlock, ODESystem.bound, List.map_map]
    exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

/-- **Existence for a contraction coordinate** `x_j' = k (c − x_j)` (`k ≥ 0`), every other
right field zero: the exponential approach is a run of every duration `ε ≥ 0` as soon as the
domain admits every state that agrees with `x` off `x_j` and has `x_j` between `x_j(0)` and
`c`. -/
theorem exists_contract_run {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    (x : State (Var n)) (j : Fin n) (k c : ℝ) (hk : 0 ≤ k)
    (hfj : ∀ s, Term.eval (fR j) s = k * (c - s (Rv j)))
    (hfo : ∀ i, i ≠ j → ∀ s, Term.eval (fR i) s = 0)
    (hdom : ∀ v, min (x (Rv j)) c ≤ v → v ≤ max (x (Rv j)) c →
      Formula.sat domR (trajJ x j (fun _ => v) 0))
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock fR (Term.const 1)) domR x ε Φ := by
  refine ⟨_, trajJ_sol x j (fun t => c + (x (Rv j) - c) * Real.exp (-(k * t))) ε hε
    (by simp) (fun t _ _ => ?_) (fun i hi t _ _ => hfo i hi _) (fun t ht _ => ?_)⟩
  · rw [hfj]; simp only [trajJ_j]
    exact hasDerivAt_expApproach k c (x (Rv j)) t
  · obtain ⟨h1, h2⟩ := exp_approach_between k c (x (Rv j)) t hk ht
    have h := hdom _ h1 h2
    have he : trajJ x j (fun _ => c + (x (Rv j) - c) * Real.exp (-(k * t))) 0
        = trajJ x j (fun t => c + (x (Rv j) - c) * Real.exp (-(k * t))) t := by
      funext y; simp [trajJ]
    rwa [he] at h

/-- **Existence for a constant-rate coordinate** `x_j' = a`, every other right field zero:
the linear motion `x_j + a t` is a run of duration `ε ≥ 0` as soon as the domain admits
every state that agrees with `x` off `x_j` and has `x_j` between `x_j(0)` and
`x_j(0) + a ε`. -/
theorem exists_rate_run {fR : Fin n → Term (Var n)} {domR : Formula (Var n)}
    (x : State (Var n)) (j : Fin n) (a : ℝ)
    (hfj : ∀ s, Term.eval (fR j) s = a)
    (hfo : ∀ i, i ≠ j → ∀ s, Term.eval (fR i) s = 0)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdom : ∀ t, 0 ≤ t → t ≤ ε → Formula.sat domR (trajJ x j (fun _ => x (Rv j) + a * t) 0)) :
    ODESol (rightBlock fR (Term.const 1)) domR x ε (trajJ x j (fun t => x (Rv j) + a * t)) := by
  refine trajJ_sol x j (fun t => x (Rv j) + a * t) ε hε (by simp) (fun t _ _ => ?_)
    (fun i hi t _ _ => hfo i hi _) (fun t ht hte => ?_)
  · rw [hfj]
    simpa using ((hasDerivAt_id t).const_mul a).const_add (x (Rv j))
  · have h := hdom t ht hte
    have he : trajJ x j (fun _ => x (Rv j) + a * t) 0 = trajJ x j (fun t => x (Rv j) + a * t) t := by
      funext y; simp [trajJ]
    rwa [he] at h

/-! ## Graphs built from an index list -/

/-- In a graph whose edges are an index list mapped through an edge constructor (every
instance's `Gr`), an edge out of `q` is a listed pair `(q, e.tgt)`. -/
theorem edgesFrom_mem_list {G : SearchGraph (Var n)} {L : List (ℕ × ℕ)}
    {f : ℕ × ℕ → REdge (Var n)} (hG : G.edges = L.map f)
    (hf : ∀ p, (f p).src = p.1 ∧ (f p).tgt = p.2) {q : ℕ} {e : REdge (Var n)}
    (he : e ∈ G.edgesFrom q) : (q, e.tgt) ∈ L := by
  obtain ⟨hmem, hsrc⟩ := List.mem_filter.mp he
  rw [hG] at hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
  have h1 := (hf p).1
  have h2 := (hf p).2
  simp only [decide_eq_true_eq] at hsrc
  rw [h2, ← hsrc, h1]
  exact hp

/-! ## Refutation -/

/-- **`WellFormedR` is false** as soon as one mode has a guard-and-domain state and one run
of duration at most `ε` from it that ends outside the guard of every declared successor. -/
theorem not_wellFormedR_of_run {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {ε : ℝ} {q : ℕ} {m : RMode (Var n)} (hm : G.modeAt q = some m)
    {x : State (Var n)} (hg : Formula.sat (guard q) x) (hd : Formula.sat m.dom x)
    {t : ℝ} {Φ : ℝ → State (Var n)} (ht : t ≤ ε) (H : ODESol m.sys m.dom x t Φ)
    (hout : ∀ e ∈ G.edgesFrom q, ¬ Formula.sat (guard e.tgt) (Φ t)) :
    ¬ WellFormedRMode G guard ε q := by
  intro h
  obtain ⟨e, he, hsat⟩ := (h m hm x hg hd trivial).2 t Φ ht H
  exact hout e he hsat

theorem not_wellFormedR_of_mode {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {ε : ℝ} {q : ℕ} (hq : q < G.modes.length) (h : ¬ WellFormedRMode G guard ε q) :
    ¬ WellFormedR G guard ε :=
  fun hw => h (hw q hq)

/-- **`WellFormedR` is false** when one mode has a guard-and-domain state from which no run
of duration `ε` exists (clause (i) fails). -/
theorem not_wellFormedR_of_noRun {G : SearchGraph (Var n)} {guard : ℕ → Formula (Var n)}
    {ε : ℝ} {q : ℕ} {m : RMode (Var n)} (hm : G.modeAt q = some m)
    {x : State (Var n)} (hg : Formula.sat (guard q) x) (hd : Formula.sat m.dom x)
    (hno : ∀ Φ, ¬ ODESol m.sys m.dom x ε Φ) : ¬ WellFormedRMode G guard ε q := by
  intro h
  obtain ⟨Φ, hΦ⟩ := (h m hm x hg hd trivial).1
  exact hno Φ hΦ

end RelCertifier

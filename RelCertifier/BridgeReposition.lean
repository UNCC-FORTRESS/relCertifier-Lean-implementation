/-
GAP 1 core — genuine multi-flow, budget-fixed cuts. The construction machinery for one left residence
during which the right switches modes several times (the right runs "faster" than the left).

The load-bearing idea: the segment boundaries are **budget-triggered**, at a FIXED clock duration
`dt = ε_r/λ` per segment, NOT a run-dependent first-passage (see the trigger analysis — the cover's
`decideCovered` recurses on the budget, so the cut is the certificate's budget unit, not where a
trajectory exits a domain). Contents, in composition order:

* Fixed-cut tiling — `plantSteps`, `plantT_zero`, `plantT_split_iter`: a single clocked left run of
  duration `k·dt` splits into exactly `k` fixed-`dt` segments (verified arithmetic `Σ = k·dt`).
* Piece 1, the bounded coupling — `faModalB` (∀∃ over left runs of clocked duration ≤ `dt`) and
  `faModal_ODE_G'_bounded`: the `dt`-bound is a PREDICATE on the run (`plantT`), NOT a narrowing of the
  domain — the mode's real evolution domain stays intact.
* Piece 2, the clock bridge — `clkGuard`/`clockedSeg`, `faModalB_clockedSeg_iff` (the fresh-clock test
  `?(tg ≤ dt)` ≡ the plantT predicate), `multiseg_clocked` (compose `k` couplings via banked
  `faModal_seq`).
* Piece 3, the clock-lift collapse — `clockLift_one`/`clockLift_chain`/`clockLift_collapse`: reduce the
  `k`-fold clocked left back to the single physical left flow, the transfer riding on `tg`-invisibility
  (the right never reads the clock).
* The mv-lift — `hstep_single_multi`, `hstep_assembled_multi`: lift `bigSeq rights` → the faithful
  `star (rightAutomatonBody G mv)` (each switch a declared `G`-edge, mode-validity `mvValid` riding the
  whole fold via `faithful_rights_bridge`), and compose over left modes with `faModal_bigChoiceL` into
  the star-right hstep that `relational_loop_multi` consumes.
* Repositions — `reposition_step_pres` (static: zero-motion + `mv`-invisibility) and
  `dynreposition_faModal` (dynamic: `segment_faModal` at `fL = 0`, the frozen-left flow).

⊤-edge model / clock are mechanization devices with no direct paper analog; the soundness lines
(`plantT`-predicate not domain-narrowing, `tg`/`mv`-invisibility, declared-edge faithfulness) are
load-bearing and called out at each lemma.
-/
import RelCertifier.JointBridge
import RelCertifier.Reify
import RelCertifier.PicardBridge
import RelCertifier.MultiSeg
import RelCertifier.BridgeUnit2
import DLCalTiming.PlantT

namespace RelCertifier
open DL DLCalTiming Function Set

variable {n : ℕ}

/-! ## The collapse — fixed budget-unit cuts (the tiling is VERIFIED, not assumed)

**Resolved from the cover code (the gate):** the segment switch is **budget/clock-triggered**,
not a `domR`-exit first-passage.

* `Checker.decideCovered` recurses on the budget `B`, decrementing by `m.weight`; the base case is
  `B ≤ m.weight` (one residence closes the budget). The switch is at the budget boundary.
* `Cover`'s `weight : ℕ` is a joint-residence budget unit (`weightPos`), *not* a domain-exit time.
* `ClockReduce`/`plantT`: a clock `tg` (`tg' = 1`) **states** the duration-bounded segment; `plantT`
  bounds `ν tg − ω tg ≤ T`. The segment's duration is fixed by the clock budget, then the clock is
  eliminated (`clockReduce`).
* `HExistDischarge`: `hExist` supplies the right witness for **any** `s` where the left stays in
  `domL` over `[0,s]`, with the right guaranteed in `domR` over the same `[0,s]` (the `hsmax` growth
  bound). So the right never needs a `domR`-exit first-passage — it stays in `domR` for the whole
  fixed-budget segment.

Hence the collapse cuts the left flow at the **fixed** clock times `dt = ε_r/λ`. `plantT_split`
(dL-caltiming, Prop 10) is the banked fixed-cut split: it cuts a `plantT⟨T1+T2⟩` run at the clock
value `T1` (a *fixed* budget quantity, the same for every run — `min r T1` in its proof). Iterating
it tiles `[0, k·dt]` into `k` pieces each of duration `dt`, and the tiling is **fixed arithmetic**
(`(k+1)·dt = dt + k·dt`), **not** an assumed or run-dependent decomposition. -/

/-- `k` consecutive `R`-steps from `ω` to `ν` (exactly `k`, unlike `ReflTransGen`). The collapse's
tiling record: each step is one fixed-duration budget segment. -/
def plantSteps (R : State (Var n) → State (Var n) → Prop) :
    ℕ → State (Var n) → State (Var n) → Prop
  | 0,     ω, ν => ω = ν
  | k + 1, ω, ν => ∃ μ, R ω μ ∧ plantSteps R k μ ν

/-- A zero-budget clocked run is the identity: `tg' = 1` forces the duration `r = ν tg − ω tg ≤ 0`
with `r ≥ 0`, hence `r = 0`, hence `ω = ν`. The base of the fixed-cut tiling. -/
theorem plantT_zero (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) (tg : Var n)
    (htg : (tg, Term.const 1) ∈ sys) {ω ν : State (Var n)}
    (h : plantT (Program.ode sys ϕ) tg 0 ω ν) : ω = ν := by
  obtain ⟨⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩, hle⟩ := h
  have H : ODESol sys ϕ ω r Φ := ⟨hr, hΦ0, hder, hmask, hdom⟩
  have haff := tg_track H htg
  have hrmem : r ∈ Icc (0 : ℝ) r := right_mem_Icc.mpr hr
  have hΦ0tg : Φ 0 tg = ω tg := congrFun hΦ0 tg
  have hνtg : ν tg = ω tg + r := by rw [← hΦr, haff r hrmem, hΦ0tg]
  have hr0 : r = 0 := le_antisymm (by rw [hνtg] at hle; linarith) hr
  rw [← hΦ0, ← hΦr, hr0]

/-- **The iterated fixed-cut split (the collapse's heart).** A single clocked left run of duration
`k·dt` splits into **exactly `k`** consecutive segments each of the **fixed** budget duration `dt`.
Every cut is at a fixed clock value (`plantT_split`, Prop 10); the tiling `k·dt = dt + ⋯ + dt` is
verified by arithmetic in the induction, never assumed. This is the budget-triggered collapse: no
`domR`-exit first-passage, no run-dependent cut. -/
theorem plantT_split_iter (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (hdt : 0 ≤ dt) (htg : (tg, Term.const 1) ∈ sys) :
    ∀ (k : ℕ) {ω ν : State (Var n)},
      plantT (Program.ode sys ϕ) tg ((k : ℝ) * dt) ω ν →
      plantSteps (fun a b => plantT (Program.ode sys ϕ) tg dt a b) k ω ν := by
  intro k
  induction k with
  | zero =>
      intro ω ν h
      simp only [Nat.cast_zero, zero_mul] at h
      exact plantT_zero sys ϕ tg htg h
  | succ k ih =>
      intro ω ν h
      have hsplit : plantT (Program.ode sys ϕ) tg (dt + (k : ℝ) * dt) ω ν := by
        rwa [show dt + (k : ℝ) * dt = ((k + 1 : ℕ) : ℝ) * dt by push_cast; ring]
      obtain ⟨μ, hfirst, hrest⟩ :=
        plantT_split sys ϕ tg dt ((k : ℝ) * dt) hdt (by positivity) htg ω ν hsplit
      exact ⟨μ, hfirst, ih hrest⟩

/-! ### Piece 1 — the per-segment plantT-coupling (the real construction content)

The clock accumulates across pieces, so each right mode's coupling is stated over a **`plantT⟨dt⟩`
bounded-duration** left run — the `dt`-bound carried as the **plantT predicate on the run**
(`ν tg − ω tg ≤ dt`), NOT as a narrowing of the domain. This is the sound line held throughout:
`domR` stays the mode's real evolution domain (unnarrowed); only the *run's duration* is bounded.
That is exactly why the `hExist` "any `s` up to `smax`" gives the bounded-`s` coupling without
touching the domain. Each piece's `hExist` needs only its **own** `dt ≤ smax` (per-segment growth,
checked at that piece's start `ω`); the clock sums *across* pieces, never *within* one. -/

/-- **Bounded ∀∃ coupling.** Like `faModal ρ P Q φ`, but the left box ranges only over `P`-runs of
clocked duration `≤ dt` (`plantT`). The `dt`-bound is a predicate on the run; the right program `Q`
carries its **real** domain (no narrowing). -/
def faModalB (ρ : Var n ≃ Var n) (P Q : Program (Var n)) (φ : Formula (Var n))
    (tg : Var n) (dt : ℝ) (ω : State (Var n)) : Prop :=
  ∀ ν, plantT P tg dt ω ν → ∃ μ, Program.sem (Q.rename ρ) ν μ ∧ Formula.sat φ μ

/-- **The domain-restricted base rule, duration-bounded.** `faModal_ODE_G'` with the left box
restricted to `plantT⟨dt⟩`-runs: `hExist` need hold only for `s ≤ dt` (its growth stays sub-`smax`
on the short segment), and the left duration `s = ν tg − ω tg ≤ dt` is read off the clock
(`tg_track`). The joint-flow assembly (`ode_combine`/`mergeTraj`) is identical to `faModal_ODE_G'`;
the ONLY change is the bounded `hExist` invocation. The right domain `φy` is untouched. -/
theorem faModal_ODE_G'_bounded (ρ : Var n ≃ Var n) (sysX sysY : ODESystem (Var n))
    (φx φy φ : Formula (Var n)) (tg : Var n) (dt : ℝ) (ω : State (Var n))
    (htg : (tg, Term.const 1) ∈ sysX)
    (hdisj : Disjoint (sysX.boundSet ∪ sysX.readVars)
                      ((sysY.rename ρ).boundSet ∪ (sysY.rename ρ).readVars))
    (hφx : φx.fv ⊆ sysX.boundSet ∪ sysX.readVars)
    (hφy : (φy.rename ρ).fv ⊆ (sysY.rename ρ).boundSet ∪ (sysY.rename ρ).readVars)
    (hP2 : Formula.sat (Formula.box
        (Program.ode (sysX ++ sysY.rename ρ) (Formula.and φx (φy.rename ρ))) φ) ω)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → s ≤ dt → ΦL 0 = ω →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ sysX,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ sysX.bound → ΦL t x = ω x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat φx (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ sysY.rename ρ,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (sysY.rename ρ).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat (φy.rename ρ) (ΦR t))) :
    faModalB ρ (Program.ode sysX φx) (Program.ode sysY φy) φ tg dt ω := by
  classical
  set ξY := sysY.rename ρ with hξ
  set ξφy := φy.rename ρ with hξφ
  intro ν hplant
  obtain ⟨⟨s, ΦL, hs, hΦL0, hΦLs, hLder, hLmaskF, hLdom⟩, hbound⟩ := hplant
  -- the bound: the clock reads the duration `s`, so `s = ν tg − ω tg ≤ dt`
  have hsdt : s ≤ dt := by
    have H : ODESol sysX φx ω s ΦL := ⟨hs, hΦL0, hLder, hLmaskF, hLdom⟩
    have haff := tg_track H htg
    have hsmem' : s ∈ Icc (0 : ℝ) s := right_mem_Icc.mpr hs
    have : ΦL s tg = ΦL 0 tg + s := haff s hsmem'
    rw [hΦLs, hΦL0] at this
    have hνtg : ν tg = ω tg + s := this
    rw [hνtg] at hbound; linarith
  obtain ⟨ΦR, hΦR0, hRder, hRmaskν, hΦRdom⟩ := hExist s ΦL hs hsdt hΦL0 hLder hLmaskF hLdom
  have hsmem : s ∈ Icc (0 : ℝ) s := right_mem_Icc.mpr hs
  have hdl := Set.disjoint_left.mp hdisj
  have hLmaskR : ∀ t ∈ Icc (0 : ℝ) s, ∀ x ∈ sysX.readVars, x ∉ sysX.bound → ΦL t x = ω x :=
    fun t ht x _ hxb => hLmaskF t ht x hxb
  have hRmaskR : ∀ t ∈ Icc (0 : ℝ) s, ∀ x ∈ ξY.readVars, x ∉ ξY.bound → ΦR t x = ω x := by
    intro t ht x hxr hxb
    have hxnX : x ∉ sysX.bound := fun hc =>
      hdl (subset_union_left hc) (subset_union_right hxr)
    rw [hRmaskν t ht x hxb, hLmaskF s hsmem x hxnX]
  have hR0 : ∀ x ∈ ξY.bound, ΦR 0 x = ω x := by
    intro x hxb
    have hxnX : x ∉ sysX.bound := fun hc =>
      hdl (subset_union_left hc) (subset_union_left hxb)
    rw [hΦR0, hLmaskF s hsmem x hxnX]
  obtain ⟨hΦ0, hagL, hagR, hJder, hJmask⟩ :=
    ode_combine sysX ξY hdisj ω s ΦL ΦR hΦL0 hR0 hLmaskR hRmaskR hLder hRder
  set Φ := mergeTraj ω sysX ξY ΦL ΦR with hΦ
  have hφxΦ : ∀ t ∈ Icc (0 : ℝ) s, Formula.sat φx (Φ t) := by
    intro t ht
    exact (Formula.coincidence φx ((hagL t ht).mono hφx)).mpr (hLdom t ht)
  have hξyΦ : ∀ t ∈ Icc (0 : ℝ) s, Formula.sat ξφy (Φ t) := by
    intro t ht
    exact (Formula.coincidence ξφy ((hagR t ht).mono hφy)).mpr (hΦRdom t ht)
  have hμeq : ΦR s = Φ s := by
    funext x
    by_cases hxbY : x ∈ ξY.bound
    · have hxnX : x ∉ sysX.bound := fun hc => hdl (subset_union_left hc) (subset_union_left hxbY)
      simp only [hΦ, mergeTraj, if_neg hxnX, if_pos hxbY]
    · have hRsx : ΦR s x = ΦL s x := by rw [hRmaskν s hsmem x hxbY]
      by_cases hxbX : x ∈ sysX.bound
      · simp only [hΦ, mergeTraj, if_pos hxbX]; exact hRsx
      · simp only [hΦ, mergeTraj, if_neg hxbX, if_neg hxbY]
        rw [hRsx, hLmaskF s hsmem x hxbX]
  refine ⟨ΦR s, ?_, ?_⟩
  · refine ⟨s, ΦR, hs, hΦR0.trans hΦLs, rfl, hRder, ?_, ?_⟩
    · intro t ht x hx; rw [hRmaskν t ht x hx, ← hΦLs]
    · intro t ht
      exact (Formula.coincidence ξφy ((hagR t ht).mono hφy)).mp (hξyΦ t ht)
  · rw [hμeq]
    rw [sat_box] at hP2
    have hfull : Program.sem (Program.ode (sysX ++ ξY) (Formula.and φx ξφy)) ω (Φ s) := by
      refine ⟨s, Φ, hs, hΦ0, rfl, hJder, hJmask, ?_⟩
      intro t ht
      exact ⟨hφxΦ t ht, hξyΦ t ht⟩
    exact hP2 (Φ s) hfull

/-! ### Piece 2 — the `faModalB ⟺ clockedSeg` bridge (the last soundness obligation)

`clockedSeg` runs the left mode under a fresh clock `tg` (reset to `0`, `tg' = 1`) followed by a
**test on the clock** `?(tg ≤ dt)`. The bridge shows this equals the bounded coupling `faModalB`:

* **(i) the guard is on the clock, ≡ the plantT predicate.** The post-reset test `?(tg ≤ dt)` fires
  iff `ν tg ≤ dt`; with `tg` reset to `0` at segment start, `ν tg = ν tg − σ₀ tg`, so the test is
  **exactly** the plantT duration bound `plantT (ode …) tg dt σ₀ ν`. Proven as an `↔` below — the
  test and the predicate are interderivable, not merely one-directional.
* **(ii) `domR` unnarrowed.** The right factor `Q` is **unchanged** across the bridge (same `Q` in
  `faModalB` and in `clockedSeg`'s diamond). `Q = ode (rightBlock …) domR` keeps the mode's real
  evolution domain. The clock touches only `tg`: `clk tg leftSys` appends `(tg, 1)` to the **left**
  system, and the guard reads only `tg` — with `tg` fresh (`tg ∉ φy.fv`, `tg ∉` physical vars) the
  guard is provably distinct from any narrowing of `domR`. That freshness is what makes "guard on
  the clock" ≠ "narrow the domain."

`clkGuard tg dt = ?(tg ≤ dt)`; `clockedSeg = (tg := 0); ode (clk tg leftSys) domL; ?(tg ≤ dt)`. -/

/-- The fresh-clock duration guard `?(tg ≤ dt)`. -/
def clkGuard (tg : Var n) (dt : ℝ) : Formula (Var n) :=
  Formula.cmp CompOp.le (Term.var tg) (Term.const dt)

@[simp] theorem sat_clkGuard (tg : Var n) (dt : ℝ) (ν : State (Var n)) :
    Formula.sat (clkGuard tg dt) ν ↔ ν tg ≤ dt := by
  simp only [clkGuard, Formula.sat, Term.eval, CompOp.interp]

/-- One clocked segment: reset the fresh clock, evolve the left under it, test the clock ≤ `dt`. -/
def clockedSeg (leftSys : ODESystem (Var n)) (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) :
    Program (Var n) :=
  Program.seq (Program.assign tg (Term.const 0))
    (Program.seq (Program.ode (clk tg leftSys) domL) (Program.test (clkGuard tg dt)))

/-- **The bridge (`↔`).** The `clockedSeg` faModal at `σ` equals the bounded coupling `faModalB` at
the reset state `σ[tg ↦ 0]`. The post-reset clock test `?(tg ≤ dt)` and the plantT duration
predicate are **interderivable** — confirming (i). `Q` (hence `domR`) is untouched — confirming
(ii). No freshness needed for the equivalence itself (pure unfolding); freshness is the *semantic*
distinctness of the clock guard, carried explicitly downstream (clk-disjointness). -/
theorem faModalB_clockedSeg_iff (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (Q : Program (Var n)) (φ : Formula (Var n)) (tg : Var n) (dt : ℝ) (σ : State (Var n)) :
    Formula.sat (faModal (Equiv.refl (Var n)) (clockedSeg leftSys domL tg dt) Q φ) σ ↔
      faModalB (Equiv.refl (Var n)) (Program.ode (clk tg leftSys) domL) Q φ tg dt
        (Function.update σ tg 0) := by
  have hσ0tg : Function.update σ tg (0 : ℝ) tg = 0 := Function.update_self tg 0 σ
  rw [faModal_sat]
  constructor
  · -- faModal clockedSeg → faModalB
    intro h ν hplant
    obtain ⟨hsem, hbound⟩ := hplant
    -- build the clockedSeg run σ → ν and read off the diamond
    have hrun : Program.sem (clockedSeg leftSys domL tg dt) σ ν := by
      refine ⟨Function.update σ tg 0, ⟨hσ0tg, fun y hy => Function.update_of_ne hy 0 σ⟩, ν, hsem, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [sat_clkGuard]
      have : ν tg - Function.update σ tg (0 : ℝ) tg ≤ dt := hbound
      rw [hσ0tg] at this; linarith
    exact h ν hrun
  · -- faModalB → faModal clockedSeg
    intro h ν hrun
    obtain ⟨σ0, ⟨hσ0, hσ0rest⟩, ν0, hode, hν0eq, hguard⟩ := hrun
    -- the assign fixes σ0 = σ[tg ↦ 0]
    have hσ0eq : σ0 = Function.update σ tg 0 := by
      funext y
      by_cases hy : y = tg
      · subst hy; rw [hσ0, hσ0tg]; simp [Term.eval]
      · rw [hσ0rest y hy, Function.update_of_ne hy 0 σ]
    subst hν0eq
    rw [sat_clkGuard] at hguard
    -- reconstruct the plantT predicate and apply faModalB
    refine h ν0 ⟨by rw [hσ0eq] at hode; exact hode, ?_⟩
    rw [hσ0tg]; linarith

/-- Forward direction: a `bigChoiceP` run is a run of one of its branches (the dispatch used to
case a `rightAutomatonBody` step onto its firing mode). -/
theorem bigChoiceP_sem_forward {ps : List (Program (Var n))} {ν μ : State (Var n)}
    (h : Program.sem (bigChoiceP ps) ν μ) : ∃ p ∈ ps, Program.sem p ν μ := by
  induction ps with
  | nil => exact absurd h (by simp [bigChoiceP, Program.sem, Formula.sat])
  | cons a as ih =>
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨p, hp, hsem⟩ := ih h; exact ⟨p, List.mem_cons_of_mem _ hp, hsem⟩

/-- The empty ODE system is the identity: every variable is unbound, so the mask freezes it. -/
theorem sem_ode_nil {dom : Formula (Var n)} {ν μ : State (Var n)}
    (h : Program.sem (Program.ode [] dom) ν μ) : μ = ν := by
  obtain ⟨r, Φ, hr, _, hΦr, _, hmask, _⟩ := h
  funext x
  rw [← hΦr, hmask r ⟨hr, le_refl r⟩ x (by simp [ODESystem.bound])]

/-- **(A) — static reposition preserves `invLe g`.** A `modeStep` at a zero-motion (`m.sys = []`)
mode is a state-preserving declared-edge mode switch; `invLe g` survives because the continuous
state is unchanged and the `mv`-assign is invisible to `g` (`mv ∉ g.fv`). -/
theorem reposition_step_pres (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (g : Term (Var n)) (hg : mv ∉ g.fv) (hsys : m.sys = [])
    {ν μ : State (Var n)} (hsem : Program.sem (modeStep G mv q m) ν μ)
    (hinv : Formula.sat (invLe g) ν) : Formula.sat (invLe g) μ := by
  -- modeStep = test(mode=q) ; ode m.sys dom ; bigChoiceP (edges)
  obtain ⟨κ1, htest, κ2, hode, hjump⟩ := hsem
  -- test passes: κ1 = ν
  have e1 : κ1 = ν := htest.1.symm
  -- empty ODE is the identity: κ2 = ν
  rw [hsys, e1] at hode
  have e2 : κ2 = ν := sem_ode_nil hode
  rw [e2] at hjump
  -- the jump is a declared edge's `test e.guard ; assign mv := e.tgt`
  obtain ⟨p, hpmem, hpsem⟩ := bigChoiceP_sem_forward hjump
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpmem
  obtain ⟨κ3, hg3, hasgn⟩ := hpsem
  have e3 : κ3 = ν := hg3.1.symm
  rw [e3] at hasgn
  -- `assign` sem is pointwise: `hasgn.2 : ∀ y ≠ mv, μ y = ν y`; on `g.fv` (which excludes `mv`)
  -- `μ` agrees with `ν`, so `invLe g` transfers by coincidence.
  have heq : Set.EqOn ν μ (invLe g).fv := by
    intro x hx
    have hxne : x ≠ mv := by
      rintro rfl
      exact hg (by simpa only [invLe, Formula.fv, Term.fv, Set.union_empty] using hx)
    exact (hasgn.2 x hxne).symm
  exact (Formula.coincidence (invLe g) heq).mp hinv

/-- **(B) — dynamic reposition = flow machinery with `fL = 0`.** The dynamic reposition's right
segment evolves under the frozen-left field `m.dynSys = jointSys (0) fR lam` (`ṡ_L = 0`); its cert
`repoDynPresPre : SegPreservesOn g m.dynSys m.dynDomPre` is exactly the joint `BoxLe` that
`segment_faModal` consumes with `fL := 0`. So its modality image is the SAME `⟨ode rightBlock⟩`
diamond as the flow case — genuine reuse, NOT a new lemma. This wrapper makes the instantiation
explicit and confirms `fL = 0` presents no obstruction (the `hdisj`/footprint side-conditions hold:
`leftBlock 0` reads nothing, so it is disjoint from the right block). -/
theorem dynreposition_faModal (g : Term (Var n)) (fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock (fun _ => Term.const 0)).boundSet ∪
                        (leftBlock (fun _ => Term.const 0)).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock (fun _ => Term.const 0)).boundSet ∪
             (leftBlock (fun _ => Term.const 0)).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys (fun _ => Term.const 0) fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock (fun _ => Term.const 0),
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock (fun _ => Term.const 0)).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock (fun _ => Term.const 0)) domL)
      (Program.ode (rightBlock fR lam) domR) (invLe g)) ν :=
  segment_faModal g (fun _ => Term.const 0) fR lam domL domR ν hdisj hφL hφR hcert hExist

/-- **Piece 1 core — the ODE-semigroup split.** A single left flow splits at any interior time `t`
into two runs (`ν → Φt`, `Φt → μ`). Reverse of the banked `sem_ode_glue`; proven by restricting the
integral curve to `[0,t]` and shifting it to `[t,r]`. This is the general form; the zero-padding
`sem_ode_sub_piter` (one real factor) is its `t = 0` / `t = r` degenerate case. Flow segments split
off a `t > 0` piece; reposition segments are the `t = 0` (zero-duration) case. -/
theorem sem_ode_split {sys : ODESystem (Var n)} {dom : Formula (Var n)} (hwf : sys.WellFormed)
    {ν μ : State (Var n)} (h : Program.sem (Program.ode sys dom) ν μ) :
    ∀ {r : ℝ} {Φ : ℝ → State (Var n)}, 0 ≤ r → Φ 0 = ν → Φ r = μ →
      (∀ t ∈ Icc (0:ℝ) r, HasDerivWithinAt (fun s => Φ s) (odeField sys (Φ t)) (Icc 0 r) t) →
      (∀ t ∈ Icc (0:ℝ) r, Formula.sat dom (Φ t)) →
      ∀ t, t ∈ Icc (0:ℝ) r →
        Program.sem (Program.ode sys dom) ν (Φ t) ∧
        Program.sem (Program.ode sys dom) (Φ t) μ := by
  intro r Φ hr hΦ0 hΦr hcΦ hdΦ t ht
  constructor
  · -- first piece [0,t]: restrict Φ
    refine (sem_ode_iff_integralCurve hwf).mpr ⟨t, Φ, ht.1, hΦ0, rfl, ?_, ?_⟩
    · intro s hs
      exact (hcΦ s ⟨hs.1, hs.2.trans ht.2⟩).mono (Set.Icc_subset_Icc (le_refl 0) ht.2)
    · intro s hs; exact hdΦ s ⟨hs.1, hs.2.trans ht.2⟩
  · -- second piece [t,r]: shift Φ by t
    refine (sem_ode_iff_integralCurve hwf).mpr ⟨r - t, fun s => Φ (t + s), by linarith [ht.2],
      by simp, by simp [hΦr], ?_, ?_⟩
    · intro s hs
      have hts : t + s ∈ Icc (0:ℝ) r := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
      have hcomp : HasDerivWithinAt (fun u : ℝ => t + u) (1 : ℝ) (Icc 0 (r - t)) s :=
        (hasDerivWithinAt_id s (Icc 0 (r - t))).const_add t
      have hmaps : Set.MapsTo (fun u : ℝ => t + u) (Icc 0 (r - t)) (Icc 0 r) :=
        fun u hu => ⟨by linarith [ht.1, hu.1], by linarith [hu.2]⟩
      have := (hcΦ (t + s) hts).scomp s hcomp hmaps
      rwa [one_smul] at this
    · intro s hs; exact hdΦ (t + s) ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩

/-- Disjointness lifts over `bigSeq`: disjoint from every piece ⟹ disjoint from the sequence. -/
theorem disjoint_vars_bigSeq {A : Set (Var n)} :
    ∀ {L : List (Program (Var n))}, (∀ q ∈ L, Disjoint A (Program.vars q)) →
      Disjoint A (Program.vars (bigSeq L))
  | [], _ => by simp [bigSeq, Program.vars, Program.fv, Program.bv, Formula.fv]
  | q :: qs, h => by
      have htail := disjoint_vars_bigSeq (fun r hr => h r (List.mem_cons_of_mem q hr))
      have hsub : Program.vars (bigSeq (q :: qs)) ⊆
          Program.vars q ∪ Program.vars (bigSeq qs) := by
        intro x hx
        simp only [bigSeq, Program.vars, Program.fv, Program.bv, Set.mem_union, Set.mem_diff] at hx ⊢
        tauto
      exact (Set.disjoint_union_right.mpr ⟨h q (List.mem_cons_self ..), htail⟩).mono_right hsub

/-- **Piece 1 — the general MULTI composition.** A single left flow couples with a right segment
sequence `bigSeq (map snd pairs)`, where each segment couples with its OWN left factor `p.1`
(`p.1 = ode leftBlock` for a flow segment, `test ⊤` for a zero-time reposition). Composed
segment-by-segment via `faModal_seq` — the per-segment coupling, replacing `multiseg_het`'s
over-restrictive uniform hypothesis. Flow and reposition are the two `p.1` shapes; no class split. -/
theorem multiseg_gen (φinv : Formula (Var n)) :
    ∀ (pairs : List (Program (Var n) × Program (Var n))),
      (∀ p ∈ pairs, ∀ q ∈ pairs,
          Disjoint (Program.vars (p.2.rename (Equiv.refl (Var n)))) (Program.vars q.1)) →
      (∀ p ∈ pairs, ∀ σ, Formula.sat φinv σ →
          Formula.sat (faModal (Equiv.refl (Var n)) p.1 p.2 φinv) σ) →
      ∀ ω, Formula.sat φinv ω →
        Formula.sat (faModal (Equiv.refl (Var n)) (bigSeq (pairs.map Prod.fst))
          (bigSeq (pairs.map Prod.snd)) φinv) ω := by
  intro pairs
  induction pairs with
  | nil =>
      intro _ _ ω hω
      simp only [List.map_nil, bigSeq]
      rw [faModal_sat]
      intro ν hν
      rw [sem_test] at hν
      obtain ⟨rfl, _⟩ := hν
      exact ⟨ω, by rw [rename_test, sem_test]; exact ⟨rfl, trivial⟩, hω⟩
  | cons p rest ih =>
      intro hdis hcouple ω hω
      simp only [List.map_cons, bigSeq]
      refine faModal_seq (Equiv.refl (Var n)) p.1 (bigSeq (rest.map Prod.fst)) p.2
        (bigSeq (rest.map Prod.snd)) φinv ω ?_ ?_
      · -- Disjoint (vars (p.2.rename id)) (vars (bigSeq (rest.map fst)))
        refine disjoint_vars_bigSeq ?_
        intro r hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact hdis p (List.mem_cons_self ..) q (List.mem_cons_of_mem p hq)
      · refine faModal_MR (Equiv.refl (Var n)) p.1 p.2 φinv _ ω
          (hcouple p (List.mem_cons_self ..) ω hω) ?_
        intro μ hμ
        exact ih (fun a ha b hb => hdis a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb))
          (fun a ha => hcouple a (List.mem_cons_of_mem p ha)) μ hμ

/-- **Composition of the bridged bounded couplings.** Feeds the per-segment bounded couplings
(`faModalB`, one right mode each) through the bridge (`faModalB_clockedSeg_iff`) into the banked
lockstep `multiseg_gen` (`faModal_seq`). Result: the `k = |rights|`-fold `clockedSeg` left, paired
with the right mode-switch sequence `bigSeq rights`, preserves `φinv`. Each left factor is one
`clockedSeg` (reset-evolve-test at duration `dt`); the right genuinely switches modes across the
sequence. `domR` untouched (the couplings carry it). -/
theorem multiseg_clocked (φinv : Formula (Var n)) (leftSys : ODESystem (Var n))
    (domL : Formula (Var n)) (tg : Var n) (dt : ℝ) (rights : List (Program (Var n)))
    (hdis : ∀ Q ∈ rights, Disjoint (Program.vars (Q.rename (Equiv.refl (Var n))))
        (Program.vars (clockedSeg leftSys domL tg dt)))
    (hcouple : ∀ Q ∈ rights, ∀ σ, Formula.sat φinv σ →
        faModalB (Equiv.refl (Var n)) (Program.ode (clk tg leftSys) domL) Q φinv tg dt
          (Function.update σ tg 0))
    (ω : State (Var n)) (hω : Formula.sat φinv ω) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (bigSeq (rights.map (fun _ => clockedSeg leftSys domL tg dt)))
      (bigSeq rights) φinv) ω := by
  have hmg := multiseg_gen φinv (rights.map (fun Q => (clockedSeg leftSys domL tg dt, Q)))
    (by
      intro p hp q hq
      obtain ⟨Qp, hQp, rfl⟩ := List.mem_map.mp hp
      obtain ⟨Qq, hQq, rfl⟩ := List.mem_map.mp hq
      exact hdis Qp hQp)
    (by
      intro p hp σ hσ
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hp
      exact (faModalB_clockedSeg_iff leftSys domL Q φinv tg dt σ).mpr (hcouple Q hQ σ hσ))
    ω hω
  simpa [List.map_map, Function.comp] using hmg

/-! ### Piece 3 — the clock-lift collapse

The box contravariance: a **physical** left run realizes a `k`-fold `clockedSeg` run, so the clocked
`faModal` collapses to the physical `faModal`. Two confirmations, both the recurring patterns:

* **(i) `tg`-freshness carries the diamond transfer.** `clockLift_one` reverses `clockReduce`
  (`Φ'(t) = update (Φ t) tg t`, clock derivative `1`); the physical vars evolve identically because
  `tg ∉ sys.bound`/`readVars`/`ϕ.fv` (carried explicitly as hypotheses, not assumed). The diamond
  transfer back to the physical endpoint (`clockLift_collapse`) is `Formula.coincidence` on the
  fresh `tg` — the SAME `mv`-invisibility that discharges the reposition step (piece 1's
  `mv ∉ g.fv`). `R`, `φinv` are `tg`-free ⟹ they cannot see the clocked/physical difference.
* **(ii) `k` is the carried budget count.** The piece count is `k = |rights| = B` (the budget), and
  the cuts are the fixed `dt`-boundaries — `plantT_split_iter` (banked, tiling-verified), NOT a
  trajectory computation. `r ≤ k·dt` is the carried budget-boundary fact from the trigger
  resolution. `clockLift_chain` peels one fixed-`dt` piece per budget unit. -/

/-- **One clocked segment from a physical run (reverse of `clockReduce`).** A physical ODE run of
duration `r ≤ dt` lifts to a `clockedSeg` run: reset `tg`, run the clocked curve `Φ'(t) = Φ(t)` with
`tg ↦ t`, pass the test `tg ≤ dt`. Physical vars evolve identically (`tg` fresh); the endpoint is
`Φ r` with `tg = r`. -/
theorem clockLift_one (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgϕ : tg ∉ ϕ.fv)
    {ω : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)}
    (H : ODESol sys ϕ ω r Φ) (hrdt : r ≤ dt) :
    Program.sem (clockedSeg sys ϕ tg dt) ω (Function.update (Φ r) tg r) := by
  refine ⟨Function.update ω tg 0,
    ⟨Function.update_self tg 0 ω, fun y hy => Function.update_of_ne hy 0 ω⟩,
    Function.update (Φ r) tg r, ?_, rfl, ?_⟩
  · -- clocked ODE run: curve `Φ'(t) = update (Φ t) tg t`
    refine ⟨r, fun t => Function.update (Φ t) tg t, H.hr, ?_, ?_, ?_, ?_, ?_⟩
    · -- start: update (Φ 0) tg 0 = update ω tg 0
      funext x; by_cases hx : x = tg
      · subst hx; simp only [Function.update_self]
      · simp only [Function.update_of_ne hx]; rw [H.hΦ0]
    · -- end: update (Φ r) tg r = update (Φ r) tg r
      rfl
    · -- derivatives over `clk tg sys = sys ++ [(tg,1)]`
      intro t ht p hp
      rcases List.mem_append.mp hp with hpsys | hptg
      · -- physical eq: `tg` update invisible to `p.1 ≠ tg` and to `p.2.eval`
        have hp1 : p.1 ≠ tg := fun hc => htgb (by rw [← hc]; exact List.mem_map.mpr ⟨p, hpsys, rfl⟩)
        have hfun : (fun u => Function.update (Φ u) tg u p.1) = fun u => Φ u p.1 := by
          funext u; exact Function.update_of_ne hp1 _ _
        rw [hfun]
        have hev : p.2.eval (Function.update (Φ t) tg t) = p.2.eval (Φ t) :=
          Term.coincidence p.2 (fun y hy => Function.update_of_ne
            (fun hc => htgr (by rw [← hc]; exact ⟨p, hpsys, hy⟩)) _ _)
        rw [hev]; exact H.hder t ht p hpsys
      · -- the clock equation `(tg, const 1)`: derivative of `t ↦ t` is `1`
        simp only [List.mem_singleton] at hptg; subst hptg
        simp only [Function.update_self, Term.eval]
        exact (hasDerivWithinAt_id t (Icc 0 r))
    · -- mask: `x ∉ (clk tg sys).bound` ⟹ held at `update ω tg 0`
      intro t ht x hx
      have htg_mem : tg ∈ (clk tg sys).bound := by
        simp only [clk, ODESystem.bound, List.map_append, List.map_cons, List.map_nil]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have hxtg : x ≠ tg := fun hc => hx (hc ▸ htg_mem)
      have hxsys : x ∉ sys.bound := fun hc => hx (by
        simp only [clk, ODESystem.bound, List.map_append]
        exact List.mem_append_left _ hc)
      show Function.update (Φ t) tg t x = Function.update ω tg 0 x
      rw [Function.update_of_ne hxtg t (Φ t), Function.update_of_ne hxtg 0 ω]
      exact H.hmask t ht x hxsys
    · -- domain `ϕ` (clock-free) holds along `Φ'`
      intro t ht
      exact (Formula.coincidence ϕ (fun y hy => (Function.update_of_ne
        (fun hc => htgϕ (by rw [← hc]; exact hy)) _ _))).mpr (H.hdom t ht)
  · -- the clock test `?(tg ≤ dt)` at the endpoint: `tg = r ≤ dt`
    rw [sat_clkGuard, Function.update_self]; exact hrdt

/-- **Reset absorption.** `clockedSeg` opens with `tg := 0`, so its runs are blind to the input's
`tg` value — inputs agreeing off `tg` give the same runs. -/
theorem clockedSeg_reset_input (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) (tg : Var n)
    (dt c : ℝ) {s ν' : State (Var n)}
    (h : Program.sem (clockedSeg sys ϕ tg dt) s ν') :
    Program.sem (clockedSeg sys ϕ tg dt) (Function.update s tg c) ν' := by
  obtain ⟨μ, ⟨hμtg, hμrest⟩, hrest⟩ := h
  refine ⟨μ, ⟨?_, ?_⟩, hrest⟩
  · rw [hμtg]; simp [Term.eval]
  · intro y hy
    rw [hμrest y hy, Function.update_of_ne hy c s]

/-- Restrict an `ODESol` to `[0, s]` (`s ≤ r`). -/
theorem ODESol_restrict {sys : ODESystem (Var n)} {ϕ : Formula (Var n)} {ω : State (Var n)}
    {r s : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys ϕ ω r Φ) (hs : 0 ≤ s) (hsr : s ≤ r) :
    ODESol sys ϕ ω s Φ where
  hr := hs
  hΦ0 := H.hΦ0
  hder := fun t ht p hp =>
    (H.hder t ⟨ht.1, ht.2.trans hsr⟩ p hp).mono (Set.Icc_subset_Icc le_rfl hsr)
  hmask := fun t ht => H.hmask t ⟨ht.1, ht.2.trans hsr⟩
  hdom := fun t ht => H.hdom t ⟨ht.1, ht.2.trans hsr⟩

/-- Shift an `ODESol` to start at `Φ s` (`s ≤ r`), duration `r − s`. -/
theorem ODESol_shift {sys : ODESystem (Var n)} {ϕ : Formula (Var n)} {ω : State (Var n)}
    {r s : ℝ} {Φ : ℝ → State (Var n)} (H : ODESol sys ϕ ω r Φ) (hs : 0 ≤ s) (hsr : s ≤ r) :
    ODESol sys ϕ (Φ s) (r - s) (fun u => Φ (s + u)) where
  hr := by linarith
  hΦ0 := by simp
  hder := by
    intro t ht p hp
    have hmem : s + t ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc : HasDerivWithinAt (fun u : ℝ => s + u) 1 (Icc 0 (r - s)) t :=
      (hasDerivWithinAt_id t (Icc 0 (r - s))).const_add s
    have hmaps : Set.MapsTo (fun u : ℝ => s + u) (Icc 0 (r - s)) (Icc 0 r) :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hcomp := (H.hder (s + t) hmem p hp).comp t hc hmaps
    rw [mul_one] at hcomp; exact hcomp
  hmask := by
    intro t ht x hx
    have hmem : s + t ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsmem : s ∈ Icc (0 : ℝ) r := ⟨hs, hsr⟩
    show Φ (s + t) x = Φ s x
    rw [H.hmask (s + t) hmem x hx, H.hmask s hsmem x hx]
  hdom := by
    intro t ht
    have hmem : s + t ∈ Icc (0 : ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact H.hdom (s + t) hmem

/-- **The clock-lift chain.** A physical run of duration `r ≤ k·dt` realizes a `k`-fold `clockedSeg`
run (from any start agreeing with `ω` off the fresh `tg`), reaching a state agreeing with the
physical endpoint `Φ r` off `tg`. `k` is the **carried budget count**; cuts are the fixed
`dt`-boundaries (`dt' = min dt r` per peel), never a trajectory computation. -/
theorem clockLift_chain (sys : ODESystem (Var n)) (ϕ : Formula (Var n)) (tg : Var n) (dt : ℝ)
    (htgb : tg ∉ sys.bound) (htgr : tg ∉ sys.readVars) (htgϕ : tg ∉ ϕ.fv) (hdt : 0 ≤ dt) :
    ∀ (k : ℕ) {ω ω' : State (Var n)} {r : ℝ} {Φ : ℝ → State (Var n)},
      (∀ x, x ≠ tg → ω' x = ω x) → ODESol sys ϕ ω r Φ → r ≤ (k : ℝ) * dt →
      ∃ ν', Program.sem (bigSeq (List.replicate k (clockedSeg sys ϕ tg dt))) ω' ν' ∧
        ∀ x, x ≠ tg → ν' x = Φ r x := by
  intro k
  induction k with
  | zero =>
      intro ω ω' r Φ hω' H hr0
      simp only [Nat.cast_zero, zero_mul] at hr0
      have hr : r = 0 := le_antisymm hr0 H.hr
      refine ⟨ω', ⟨rfl, trivial⟩, ?_⟩
      intro x hx
      rw [hω' x hx, ← H.hΦ0]; congr 1; rw [hr]
  | succ k ih =>
      intro ω ω' r Φ hω' H hr1
      set dt' := min dt r with hdt'
      have hdt'0 : 0 ≤ dt' := le_min hdt H.hr
      have hdt'dt : dt' ≤ dt := min_le_left dt r
      have hdt'r : dt' ≤ r := min_le_right dt r
      -- first piece: physical run [0, dt'] lifts to one clockedSeg
      have Hpiece := ODESol_restrict H hdt'0 hdt'r
      have hfirst := clockLift_one sys ϕ tg dt htgb htgr htgϕ Hpiece hdt'dt
      -- reposition the first run to start at `ω'` (agrees with ω off tg)
      have hω'eq : ω' = Function.update ω tg (ω' tg) := by
        funext y; by_cases hy : y = tg
        · subst hy; rw [Function.update_self]
        · rw [Function.update_of_ne hy, hω' y hy]
      have hfirst' : Program.sem (clockedSeg sys ϕ tg dt) ω' (Function.update (Φ dt') tg dt') := by
        rw [hω'eq]; exact clockedSeg_reset_input sys ϕ tg dt (ω' tg) hfirst
      -- rest: shifted run [dt', r], duration `r - dt' ≤ k·dt`
      have Hshift := ODESol_shift H hdt'0 hdt'r
      have hrest_bound : r - dt' ≤ (k : ℝ) * dt := by
        rcases le_or_gt r dt with h | h
        · rw [hdt', min_eq_right h]; simp; positivity
        · rw [hdt', min_eq_left (le_of_lt h)]
          have : r ≤ ((k : ℝ) + 1) * dt := by push_cast at hr1; linarith
          nlinarith [this]
      have hstart' : ∀ x, x ≠ tg → Function.update (Φ dt') tg dt' x = Φ dt' x :=
        fun x hx => Function.update_of_ne hx dt' (Φ dt')
      obtain ⟨ν', hrun, hν'⟩ := ih hstart' Hshift hrest_bound
      -- chain: clockedSeg then the k-fold rest
      refine ⟨ν', ⟨Function.update (Φ dt') tg dt', hfirst', hrun⟩, ?_⟩
      intro x hx
      rw [hν' x hx]
      show Φ (dt' + (r - dt')) x = Φ r x
      congr 1; ring

/-- **The clock-lift collapse (box contravariance).** The clocked `k`-fold `clockedSeg` `faModal`
collapses to the **physical** `faModal id (ode leftSys domL) R φ`. A physical left run lifts to the
`k`-fold clocked run (`clockLift_chain`); the clocked faModal responds; the response transfers back
to the physical endpoint by `tg`-freshness — `R`, `φ` are `tg`-free, so `Program.coincidence`
(`tg`-invisibility, the recurring `mv ∉ g.fv` pattern) moves the run and preserves `φ`. `hbudget`
is the carried budget bound `r ≤ k·dt`. -/
theorem clockLift_collapse (leftSys : ODESystem (Var n)) (domL : Formula (Var n))
    (R : Program (Var n)) (φ : Formula (Var n)) (tg : Var n) (dt : ℝ) (k : ℕ)
    (htgb : tg ∉ leftSys.bound) (htgr : tg ∉ leftSys.readVars) (htgϕ : tg ∉ domL.fv)
    (hdt : 0 ≤ dt) (htgR : tg ∉ (R.rename (Equiv.refl (Var n))).fv) (htgφ : tg ∉ φ.fv)
    {ω : State (Var n)}
    (hbudget : ∀ {r : ℝ} {Φ : ℝ → State (Var n)}, ODESol leftSys domL ω r Φ → r ≤ (k : ℝ) * dt)
    (h : Formula.sat (faModal (Equiv.refl (Var n))
      (bigSeq (List.replicate k (clockedSeg leftSys domL tg dt))) R φ) ω) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode leftSys domL) R φ) ω := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hν
  have H : ODESol leftSys domL ω r Φ := ⟨hr, hΦ0, hder, hmask, hdom⟩
  obtain ⟨ν', hrun, hν'⟩ :=
    clockLift_chain leftSys domL tg dt htgb htgr htgϕ hdt k (fun _ _ => rfl) H (hbudget H)
  -- ν' agrees with the physical endpoint ν = Φ r off the fresh clock
  have hν'ν : Set.EqOn ν' ν {x | x ≠ tg} :=
    fun x hx => (hν' x hx).trans (congrFun hΦr x)
  obtain ⟨μ, hRrun, hφμ⟩ := h ν' hrun
  -- transfer the right run back to ν by tg-freshness (Program.coincidence)
  have hWR : (R.rename (Equiv.refl (Var n))).fv ⊆ {x | x ≠ tg} :=
    fun x hx (hc : x = tg) => htgR (hc ▸ hx)
  obtain ⟨μ₂, hRrun₂, hμμ₂⟩ := Program.coincidence (R.rename (Equiv.refl (Var n))) hWR hν'ν hRrun
  refine ⟨μ₂, hRrun₂, ?_⟩
  have hWφ : φ.fv ⊆ {x | x ≠ tg} := fun x hx (hc : x = tg) => htgφ (hc ▸ hx)
  exact (Formula.coincidence φ (hμμ₂.mono (hWφ.trans Set.subset_union_left))).mp hφμ

/-- **The per-switch faithful lift** — the real content beyond the flat `reified_relational_multi`.
One right-mode flow at a **declared** mode `q`, followed by a **declared** ⊤-guarded edge `e`
(`e ∈ edgesFrom q`, `e.tgt < modes.length` — `EdgeTargetsValid`, the flat-`R*` guardrail), becomes
one `star (rightAutomatonBody G mv)` step, threading the mode variable `q → e.tgt`. This is the
∃-right faithfulness the emitted `rights` switch must respect: it maps to a real `G`-edge, not a
flat memoryless choice. Mirrors the witness lemma's `jump` case, per segment. -/
theorem single_seg_R_real (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ) (m : RMode (Var n))
    (hfv : mv ∉ (Program.ode m.sys m.dom).fv)
    {e : REdge (Var n)} (hm : G.modeAt q = some m) (he : e ∈ G.edgesFrom q)
    (htt : e.guard = Formula.tt) (hlt : e.tgt < G.modes.length)
    {ν μ : State (Var n)} (hflow : Program.sem (Program.ode m.sys m.dom) ν μ) :
    Program.sem (Program.star (rightAutomatonBody G mv))
      (Function.update ν mv (q : ℝ)) (Function.update μ mv (e.tgt : ℝ)) := by
  have hg : Formula.sat e.guard (Function.update μ mv (q : ℝ)) := by rw [htt]; trivial
  have hstep := modeStep_sem G mv q m hfv he hflow hg
  have hbody : Program.sem (rightAutomatonBody G mv)
      (Function.update ν mv (q : ℝ)) (Function.update μ mv (e.tgt : ℝ)) := by
    refine bigChoiceP_sem_of_mem (List.mem_filterMap.mpr ⟨q, ?_, ?_⟩) hstep
    · exact List.mem_range.mpr (by
        have := hm; simp only [SearchGraph.modeAt] at this
        exact List.getElem?_eq_some_iff.mp this |>.1)
    · rw [hm]; rfl
  exact Relation.ReflTransGen.head hbody Relation.ReflTransGen.refl

/-- **The faithful multiseg-to-R_real bridge.** The emitted right mode-switch sequence `segs` (each
`(q, m, e)` a declared mode + declared ⊤-edge, consecutively chained `e.tgt = next.q`) lifts a
`bigSeq`-of-flows run into a `star (rightAutomatonBody G mv)` run, threading `mv` through the mode
sequence. **Every switch is a real `G`-edge** (`single_seg_R_real`, `EdgeTargetsValid`) — the ∃-right
faithfulness beyond flat `reified_relational_multi`, preserved end-to-end because the fold
(`ReflTransGen.trans`) concatenates per-step-faithful automaton steps. -/
theorem faithful_rights_bridge (G : SearchGraph (Var n)) (mv : Var n)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length) :
    ∀ (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
      (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) →
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs →
      ∀ (q0 : ℕ), q0 < G.modes.length → ∀ {ν μ : State (Var n)},
        (∀ s, segs.head? = some s → s.1 = q0) →
        Program.sem (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) ν μ →
        ∃ qf, qf < G.modes.length ∧ Program.sem (Program.star (rightAutomatonBody G mv))
          (Function.update ν mv (q0 : ℝ)) (Function.update μ mv (qf : ℝ)) := by
  intro segs
  induction segs with
  | nil =>
      intro _ _ q0 hq0valid _ _ _ hrun
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, _⟩ := hrun
      exact ⟨q0, hq0valid, Relation.ReflTransGen.refl⟩
  | cons s rest ih =>
      intro halign hchain q0 _ _ _ hstart hrun
      have hq0 : s.1 = q0 := hstart s rfl
      subst hq0
      simp only [List.map_cons, bigSeq] at hrun
      obtain ⟨κ, hflow, hrest⟩ := hrun
      obtain ⟨hm, he⟩ := halign s (List.mem_cons_self ..)
      have hfirst := single_seg_R_real G mv s.1 s.2.1 (hfresh s.1 s.2.1 hm) hm he
        (htt s.1 s.2.2 he) (hlt s.1 s.2.2 he) hflow
      have htailstart : ∀ t, rest.head? = some t → t.1 = s.2.2.tgt := by
        intro t ht
        rcases rest with _ | ⟨r, rs⟩
        · exact absurd ht (by simp)
        · simp only [List.head?_cons, Option.some.injEq] at ht
          subst ht; exact hchain.rel.symm
      -- the next mode `s.2.2.tgt` is a declared valid target (EdgeTargetsValid) — mvValid rides the fold
      obtain ⟨qf, hqfvalid, htail⟩ := ih (fun t ht => halign t (List.mem_cons_of_mem s ht))
        hchain.of_cons s.2.2.tgt (hlt s.1 s.2.2 he) htailstart hrest
      exact ⟨qf, hqfvalid, Relation.ReflTransGen.trans hfirst htail⟩

/-- **The bigSeq→star faithful mv-lift (per left mode).** Upgrades the genuine-multi-flow
`faModal … (bigSeq rights) (invLe g)` (from `multiseg_clocked` + `clockLift_collapse`) to the
faithful loop step `faModal … (star (rightAutomatonBody G mv)) (phiInv g mv k)`. Two banked
mechanisms carry it:
* **mv-invisibility** — `mv ∉ leftBlock.bound` (`leftBlock_frames_mv`) ⟹ `ν mv = σ mv = q`, so
  `update ν mv q = ν` (start aligns); `mv ∉ g.fv` (`Term.coincidence`) ⟹ `invLe g` transfers from
  `μ` to the mv-updated witness. The same `mv`-invisibility as the flow fragment.
* **mvValid-preservation** — the star endpoint's mode `qf` is a declared valid target
  (`qf < modes.length`, from `faithful_rights_bridge` threading `EdgeTargetsValid` at **every**
  step of the fold, not just the last), so `mvValid` holds at the witness. -/
theorem hstep_single_multi (G : SearchGraph (Var n)) (mv : Var n) (q : ℕ)
    (g : Term (Var n)) (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
    (hg : mv ∉ g.fv) (hmvL : mv ∉ (leftBlock fL).bound) (hqlt : q < G.modes.length)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (segs : List (ℕ × RMode (Var n) × REdge (Var n)))
    (halign : ∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1)
    (hchain : List.IsChain (fun a b => a.2.2.tgt = b.1) segs)
    (hhead : ∀ s, segs.head? = some s → s.1 = q)
    {σ : State (Var n)} (hmvq : σ mv = (q : ℝ))
    (hfaModal : Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ) :
    Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
      (Program.star (rightAutomatonBody G mv)) (phiInv g mv G.modes.length)) σ := by
  rw [faModal_sat] at hfaModal ⊢
  intro ν hleft
  obtain ⟨μ, hbigSeq, hinvμ⟩ := hfaModal ν hleft
  have hνmv : ν mv = (q : ℝ) := (leftBlock_frames_mv fL domL mv hmvL hleft).trans hmvq
  rw [Program.rename_refl] at hbigSeq
  obtain ⟨qf, hqfvalid, hstar⟩ :=
    faithful_rights_bridge G mv hfresh htt hlt segs halign hchain q hqlt hhead hbigSeq
  have hupdν : Function.update ν mv (q : ℝ) = ν := by
    funext x; by_cases hx : x = mv
    · subst hx; rw [Function.update_self, hνmv]
    · rw [Function.update_of_ne hx]
  rw [hupdν] at hstar
  refine ⟨Function.update μ mv (qf : ℝ), by rw [Program.rename_refl]; exact hstar, ?_⟩
  rw [phiInv, sat_and]
  refine ⟨?_, ?_⟩
  · rw [sat_invLe] at hinvμ ⊢
    rwa [Term.coincidence g (fun y hy =>
      Function.update_of_ne (fun hc => hg (by rw [← hc]; exact hy)) _ _)]
  · rw [sat_mvValid]
    exact ⟨qf, hqfvalid, Function.update_self mv (qf : ℝ) μ⟩

/-- **The assembled faithful multi loop-step.** Composes the per-left-mode multi lifts
(`hstep_single_multi`) over the flat left body `bigChoice leftProgs` via `faModal_bigChoiceL`. The
current right mode `q` is read off the state (`mvValid`); each left mode's genuine-multi-flow
response (`Hmulti`: the emitted `segs` + the `bigSeq`-flow `faModal` over `invLe g`, from
`multiseg_clocked`/`clockLift_collapse`) lifts to one `star (rightAutomatonBody G mv)` response.
This is the **star-right** hstep `relational_loop_multi` consumes — one left residence ↔ a
mode-switching star, the genuine multi-flow the single-body `hstep_assembled` cannot express. -/
theorem hstep_assembled_multi (G : SearchGraph (Var n)) (mv : Var n) (g : Term (Var n))
    (leftProgs : List (Program (Var n))) (hg : mv ∉ g.fv)
    (hfresh : ∀ q m, G.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv)
    (htt : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = Formula.tt)
    (hlt : ∀ q, ∀ e ∈ G.edgesFrom q, e.tgt < G.modes.length)
    (Hmulti : ∀ P ∈ leftProgs, ∀ (q : ℕ), q < G.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (invLe g) σ →
      ∃ (fL : Fin n → Term (Var n)) (domL : Formula (Var n))
        (segs : List (ℕ × RMode (Var n) × REdge (Var n))),
        P = Program.ode (leftBlock fL) domL ∧ mv ∉ (leftBlock fL).bound ∧
        (∀ s ∈ segs, G.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ G.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var n)) (Program.ode (leftBlock fL) domL)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) (invLe g)) σ) :
    ∀ σ, Formula.sat (phiInv g mv G.modes.length) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (bigChoice leftProgs)
        (Program.star (rightAutomatonBody G mv)) (phiInv g mv G.modes.length)) σ := by
  intro σ hφ'
  obtain ⟨q, hqlt, hmvq⟩ := sat_mvValid.mp hφ'.2
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (Program.star (rightAutomatonBody G mv))
    (phiInv g mv G.modes.length) σ leftProgs ?_
  intro P hP
  obtain ⟨fL, domL, segs, hPeq, hmvL, halign, hchain, hhead, hfaModal⟩ :=
    Hmulti P hP q hqlt σ hmvq hφ'.1
  rw [hPeq]
  exact hstep_single_multi G mv q g fL domL hg hmvL hqlt hfresh htt hlt segs halign hchain hhead
    hmvq hfaModal

end RelCertifier

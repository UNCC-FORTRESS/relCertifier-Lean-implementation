/-
GAP 1 (A) — the static-reposition step-lemma.

A static-reposition mode carries `m.sys = []` (zero motion): its `modeStep` is
`test(mode=q); ode [] dom; test e.guard; assign mv := e.tgt` — a state-preserving discrete mode
switch along a DECLARED edge. It preserves `invLe g` by two banked/trivial facts: the empty ODE is
the identity on the continuous state, and the `mv`-assign is invisible to `invLe g` (`mv ∉ g.fv`).
No `RegionInvOn`, no analysis (see the C.2 resolution: `region` references the left guard, is not a
right-automaton transition, and drops out post-tightening). ∃-right jump-faithfulness is the same as
the flow case: the target is a declared `G`-edge (`e ∈ edgesFrom q`).
-/
import RelCertifier.JointBridge
import RelCertifier.Reify
import RelCertifier.PicardBridge
import RelCertifier.MultiSeg
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
      ∀ (q0 : ℕ) {ν μ : State (Var n)},
        (∀ s, segs.head? = some s → s.1 = q0) →
        Program.sem (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom))) ν μ →
        ∃ qf, Program.sem (Program.star (rightAutomatonBody G mv))
          (Function.update ν mv (q0 : ℝ)) (Function.update μ mv (qf : ℝ)) := by
  intro segs
  induction segs with
  | nil =>
      intro _ _ q0 _ _ _ hrun
      rw [List.map_nil, bigSeq, sem_test] at hrun
      obtain ⟨rfl, _⟩ := hrun
      exact ⟨q0, Relation.ReflTransGen.refl⟩
  | cons s rest ih =>
      intro halign hchain q0 _ _ hstart hrun
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
      obtain ⟨qf, htail⟩ := ih (fun t ht => halign t (List.mem_cons_of_mem s ht))
        hchain.of_cons s.2.2.tgt htailstart hrest
      exact ⟨qf, Relation.ReflTransGen.trans hfirst htail⟩

end RelCertifier

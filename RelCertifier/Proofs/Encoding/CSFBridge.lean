/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `faModal_ODE_G'` — the domain-restricted ∀∃-ODE base rule (outcome-3 fix)

dL-caltiming's `faModal_ODE_G` (`DLCalTiming.ODEJoint`) discharges the ∀∃-ODE step from three
premises, the third of which — `hP3 : [x'=θ, ξ(y'=δ)]⊤ (φx → ξφy)` — asserts that along the
**unconstrained** joint flow the left evolution domain `φx` forces the right one `ξφy`. Its only
use site in dL-caltiming is `faModal_ODE_I`, where `φx = φy = ⊤` makes `hP3` trivial.

For the **relational cover**, the left/right evolution domains constrain **disjoint** variable
blocks (`Side.L`/`Side.R`) and are tight and divergent (e.g. `θ_L∈[0,1]` vs `θ_R∈[0,1]`;
`px_L≤5` vs `px_R≤15`), so `hP3` is **false** — `φx` (over left vars) cannot imply `ξφy` (over
disjoint right vars) along the free flow. `faModal_ODE_G` is therefore the wrong base rule here.

The fix is sound and bounded. `hP3` is used at exactly **one** spot in `faModal_ODE_G`'s proof:
to build `hξyΦ : ∀ t∈[0,s], sat ξφy (Φ t)` — the joint trajectory stays in the **right** domain.
The cover's co-execution `Program.sem (ode jointSys (evolveL∧evolveR))` already stays in
`evolveR = ξφy` throughout (its ODE domain constraint). So we **drop `hP3`** and instead
**strengthen `hExist`** to hand back a right witness that provably stays in its own domain
(`∀ t, sat ξφy (ΦR t)`), from which `hξyΦ` follows by the *same* coincidence + `ode_combine`
agreement (`hagR`) already in the proof — `Φ ≡ ΦR` on right vars. The obligation is **relocated,
not removed**: from "prove `φx → ξφy` along the free flow" (false for divergent domains) to "the
witness stays in its own domain" (supplied by the cover's joint-domain co-execution).

Conclusion identical to `faModal_ODE_G`; delta is a single `have`. No new axioms.
-/
import DLCalTiming.ODEJoint

namespace RelCertifier

open DL Set DLCalTiming

variable {V : Type*}

/-- **`∀∃-ODE-G'` — domain-restricted ∀∃-ODE base rule.** As `faModal_ODE_G`, but `hP3`
(domain compatibility along the free flow) is **dropped** and `hExist` is **strengthened** to
require the right witness `ΦR` to stay in its own domain `φy.rename ρ` throughout `[0,s]`. Sound
for the relational cover, whose divergent left/right domains make `faModal_ODE_G`'s `hP3` false
but whose joint-domain co-execution supplies exactly this in-domain right witness. -/
theorem faModal_ODE_G' (ρ : V ≃ V) (sysX sysY : ODESystem V) (φx φy φ : Formula V)
    (ω : State V)
    (hdisj : Disjoint (sysX.boundSet ∪ sysX.readVars)
                      ((sysY.rename ρ).boundSet ∪ (sysY.rename ρ).readVars))
    (hφx : φx.fv ⊆ sysX.boundSet ∪ sysX.readVars)
    (hφy : (φy.rename ρ).fv ⊆ (sysY.rename ρ).boundSet ∪ (sysY.rename ρ).readVars)
    (hP2 : Formula.sat (Formula.box
        (Program.ode (sysX ++ sysY.rename ρ) (Formula.and φx (φy.rename ρ))) φ) ω)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State V), 0 ≤ s → ΦL 0 = ω →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ sysX,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ sysX.bound → ΦL t x = ω x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat φx (ΦL t)) →
        ∃ ΦR : ℝ → State V, ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ sysY.rename ρ,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (sysY.rename ρ).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat (φy.rename ρ) (ΦR t))) :
    Formula.sat (faModal ρ (Program.ode sysX φx) (Program.ode sysY φy) φ) ω := by
  classical
  set ξY := sysY.rename ρ with hξ
  set ξφy := φy.rename ρ with hξφ
  rw [faModal_sat]
  intro ν hν
  obtain ⟨s, ΦL, hs, hΦL0, hΦLs, hLder, hLmaskF, hLdom⟩ := hν
  obtain ⟨ΦR, hΦR0, hRder, hRmaskν, hΦRdom⟩ := hExist s ΦL hs hΦL0 hLder hLmaskF hLdom
  have hsmem : s ∈ Icc (0 : ℝ) s := right_mem_Icc.mpr hs
  have hdl := Set.disjoint_left.mp hdisj
  -- masks restricted to read-vars, and right start, for `ode_combine`
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
  -- φx holds along the joint flow
  have hφxΦ : ∀ t ∈ Icc (0 : ℝ) s, Formula.sat φx (Φ t) := by
    intro t ht
    exact (Formula.coincidence φx ((hagL t ht).mono hφx)).mpr (hLdom t ht)
  -- DELTA (vs `faModal_ODE_G`): `hξyΦ` now comes from the strengthened `hExist` (`hΦRdom`,
  -- the right witness stays in `ξφy`) transported to `Φ` via `hagR` (`Φ ≡ ΦR` on right vars) —
  -- the SAME coincidence used downstream — instead of from the dropped `hP3`.
  have hξyΦ : ∀ t ∈ Icc (0 : ℝ) s, Formula.sat ξφy (Φ t) := by
    intro t ht
    exact (Formula.coincidence ξφy ((hagR t ht).mono hφy)).mpr (hΦRdom t ht)
  -- the witness endpoint `ΦR s` equals the joint endpoint `Φ s`
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
  -- assemble the witness: a right run reaching `ΦR s`, satisfying `φ`
  refine ⟨ΦR s, ?_, ?_⟩
  · -- sem (ode ξY ξφy) ν (ΦR s)
    refine ⟨s, ΦR, hs, hΦR0.trans hΦLs, rfl, hRder, ?_, ?_⟩
    · intro t ht x hx; rw [hRmaskν t ht x hx, ← hΦLs]
    · intro t ht
      exact (Formula.coincidence ξφy ((hagR t ht).mono hφy)).mp (hξyΦ t ht)
  · -- φ holds at `ΦR s = Φ s`
    rw [hμeq]
    rw [sat_box] at hP2
    have hfull : Program.sem (Program.ode (sysX ++ ξY) (Formula.and φx ξφy)) ω (Φ s) := by
      refine ⟨s, Φ, hs, hΦ0, rfl, hJder, hJmask, ?_⟩
      intro t ht
      exact ⟨hφxΦ t ht, hξyΦ t ht⟩
    exact hP2 (Φ s) hfull

end RelCertifier

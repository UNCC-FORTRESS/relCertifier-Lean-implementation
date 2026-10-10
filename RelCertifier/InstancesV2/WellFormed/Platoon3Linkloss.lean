/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss`: Assumption 1 of the right model — FALSE (model defect)

Over the instance's guarded right automaton `Gr` (the repaired model,
`docs/SUITE-REDESIGN.md` §20), the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false** (`platoon3_linkloss_wellFormedR_false`): the AEB sink `BRAKE1`
(guard `g₁ < 20`, flow `g₁' = r₁`, `r₁' = 4`, the other links in `FOLLOW`; declared
successors `[BRAKE1]` only) is left by its own flow. From `g₁ = 19`, `r₁ = 0`, the other
links at rest at their set point (`g = 30`, `r = 0`), the run of duration 1 ends at
`g₁ = 21`, `r₁ = 4`, where no declared successor of `BRAKE1` is enabled. (The `BRAKE` modes
are pruned sinks: the certificate never enters them, and Theorem 3 does not depend on them.
The same holds for `BRAKE2`, `BRAKE3` by symmetry; one blocking mode refutes the predicate.)

**`FOLLOW` satisfies Assumption 1** (`platoon3_linkloss_wellFormedR_follow`, style (a),
Z3-free): its guard (the operating range) is forward invariant under the three damped links
(`Platoon3Link.link_guard_Ronly`, plus the evolve box every run keeps). Existence: the
explicit link solution (`solΦ`, `link_bounds`).
-/
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
import RelCertifier.InstancesV2.WellFormed.Platoon3Link

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2Platoon3Linkloss

open DL DLCalTiming DLRel Parse Set Platoon3Link

theorem epsR_eq : epsR platoon3_linkloss_IRv2 = 1 := by
  simp [epsR, platoon3_linkloss_IRv2, hq1_0]

noncomputable def guardR (q : ℕ) : Formula (Var 6) := hostGuard vs 6 Side.R (mR q)

/-- One link's operating range. -/
def LinkOp (x : State (Var 6)) (jx jy : Fin 6) : Prop :=
  20 ≤ x (Rv jx) ∧ x (Rv jx) ≤ 60 ∧ -10 ≤ x (Rv jy) ∧ x (Rv jy) ≤ 10 ∧
    21 ≤ x (Rv jx) + 2 * x (Rv jy) ∧ x (Rv jx) + 2 * x (Rv jy) ≤ 59

theorem sat_guardR0 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 0)) x ↔ LinkOp x 0 1 ∧ LinkOp x 2 3 ∧ LinkOp x 4 5 := by
  constructor
  · intro h
    simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq19_0, hq59_0,
      hqm10_0, hq10_0, hq2_0, hq20_0, hq58_0, hq25_0, hq21_0, hq60_0, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, AOp.interp, Rv] at h
    simp only [LinkOp, Rv]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      tauto
  · rintro ⟨h1, h2, h3⟩
    exact guardR0_of x h1 h2 h3

theorem sat_guardR1 (x : State (Var 6)) :
    Formula.sat (hostGuard vs 6 Side.R (mR 1)) x ↔ x (Rv 0) < 20 := by
  simp [hostGuard, mR, platoon3_linkloss_IRv2, Run.lowerF, Run.lowerE, hq20_0, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 6)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `FOLLOW`** (style (a), Z3-free). -/
theorem platoon3_linkloss_wellFormedR_follow :
    WellFormedRMode Gr guardR (epsR platoon3_linkloss_IRv2) 0 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  obtain ⟨h1, h2, h3⟩ := (sat_guardR0 x).mp hg
  have hbox := (sat_domR x).mp hd
  obtain ⟨L1, L2, L3⟩ := linkFields fR_field
  refine ⟨?_, ?_⟩
  · have hQ : QBounds 30 x := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h3
      obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := hbox
      simp only [QBounds, LinkStart, Q2]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        linarith
    refine ⟨solΦ 30 x, ⟨by norm_num, solΦ_zero _ _, fun t _ => solΦ_deriv 30 (fR 0) fR_field x 1 t,
      ?_, ?_⟩⟩
    · intro t _ y hy
      refine solΦ_frozen _ _ _ y (fun hyR => hy ?_)
      obtain ⟨sy, j⟩ := y
      simp only at hyR
      subst hyR
      simp only [modeW, rightBlock, ODESystem.bound, List.map_map]
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    · intro t ht
      show Formula.sat domR _
      rw [sat_domR]
      exact solΦ_box 30 (by norm_num) (by norm_num) _ hQ t ht.1
  · intro t Φ _ H
    have k1 := link_guard_Ronly (fR 0) domR 0 1 30 (by norm_num) (by norm_num) L1 H
      h1.1 h1.2.2.2.2.1 h1.2.2.2.2.2
    have k2 := link_guard_Ronly (fR 0) domR 2 3 30 (by norm_num) (by norm_num) L2 H
      h2.1 h2.2.2.2.2.1 h2.2.2.2.2.2
    have k3 := link_guard_Ronly (fR 0) domR 4 5 30 (by norm_num) (by norm_num) L3 H
      h3.1 h3.2.2.2.2.1 h3.2.2.2.2.2
    obtain ⟨⟨x0, x1, y0, y1⟩, ⟨x2, x3, y2, y3⟩, ⟨x4, x5, y4, y5⟩⟩ := (sat_domR _).mp H.end_dom
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr
      ⟨⟨k1.1, x1, y0, y1, k1.2.1, k1.2.2⟩, ⟨k2.1, x3, y2, y3, k2.2.1, k2.2.2⟩,
        ⟨k3.1, x5, y4, y5, k3.2.1, k3.2.2⟩⟩⟩

/-! ## `BRAKE1` blocks -/

theorem hq4_0 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem fR_brake1 (z : State (Var 6)) :
    Term.eval (fR 1 0) z = z (Rv 1) ∧ Term.eval (fR 1 1) z = 4 ∧
    Term.eval (fR 1 2) z = z (Rv 3) ∧
    Term.eval (fR 1 3) z = -(1/8) * (z (Rv 2) - 30) - 3/4 * z (Rv 3) ∧
    Term.eval (fR 1 4) z = z (Rv 5) ∧
    Term.eval (fR 1 5) z = -(1/8) * (z (Rv 4) - 30) - 3/4 * z (Rv 5) := by
  simp [fR, hostDyn, mR, platoon3_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hqm0_125, hq0_75,
    hq30_0, hq4_0, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]
  refine ⟨by ring, by ring⟩

/-- The witness: `g₁ = 19`, `r₁ = 0`; links 2, 3 at rest at 30; every other variable 0. -/
noncomputable def xw : State (Var 6) := fun y =>
  if y = Rv 0 then 19 else if y = Rv 2 then 30 else if y = Rv 4 then 30 else 0

/-- Its `BRAKE1` run: `g₁ = 19 + 2t²`, `r₁ = 4t`, the rest frozen. -/
noncomputable def brakeφ : Fin 6 → ℝ → ℝ := fun i t =>
  if i = 0 then 19 + 2 * t ^ 2 else if i = 1 then 4 * t else if i = 2 then 30
  else if i = 4 then 30 else 0

theorem xw_R (i : Fin 6) : xw (Rv i) = brakeφ i 0 := by
  fin_cases i <;> simp [xw, brakeφ, Rv]

/-- **Assumption 1 fails at `BRAKE1`**: from the witness the run of duration 1 ends at
`g₁ = 21`, outside `BRAKE1`'s guard; `BRAKE1`'s only declared successor is itself. -/
theorem platoon3_linkloss_brake1_blocks :
    ¬ WellFormedRMode Gr guardR (epsR platoon3_linkloss_IRv2) 1 := by
  rw [epsR_eq]
  have H : ODESol (modeW 1).sys (modeW 1).dom xw 1 (trajR xw brakeφ) := by
    refine explicit_sol xw brakeφ 1 (by norm_num) (fun i => (xw_R i).symm) ?_ ?_
    · intro i t _ _
      obtain ⟨f0, f1, f2, f3, f4, f5⟩ := fR_brake1 (trajR xw brakeφ t)
      fin_cases i
      · have hf : brakeφ 0 = fun u => 19 + 2 * u ^ 2 := by funext u; simp [brakeφ]
        show HasDerivAt (brakeφ 0) _ t
        rw [show ((⟨0, by norm_num⟩ : Fin 6)) = (0 : Fin 6) from rfl, f0, trajR_R, hf]
        refine (((hasDerivAt_pow 2 t).const_mul 2).const_add 19).congr_deriv ?_
        simp [brakeφ]; ring
      · have hf : brakeφ 1 = fun u => 4 * u := by funext u; simp [brakeφ]
        show HasDerivAt (brakeφ 1) _ t
        rw [show ((⟨1, by norm_num⟩ : Fin 6)) = (1 : Fin 6) from rfl, f1, hf]
        exact ((hasDerivAt_id t).const_mul 4).congr_deriv (by simp)
      · show HasDerivAt (brakeφ 2) _ t
        rw [show ((⟨2, by norm_num⟩ : Fin 6)) = (2 : Fin 6) from rfl, f2, trajR_R]
        have hf : brakeφ 2 = fun _ => 30 := by funext u; simp [brakeφ]
        rw [hf]; simpa [brakeφ] using hasDerivAt_const t (30:ℝ)
      · show HasDerivAt (brakeφ 3) _ t
        rw [show ((⟨3, by norm_num⟩ : Fin 6)) = (3 : Fin 6) from rfl, f3, trajR_R, trajR_R]
        have hf : brakeφ 3 = fun _ => 0 := by funext u; simp [brakeφ]
        rw [hf]; simpa [brakeφ] using hasDerivAt_const t (0:ℝ)
      · show HasDerivAt (brakeφ 4) _ t
        rw [show ((⟨4, by norm_num⟩ : Fin 6)) = (4 : Fin 6) from rfl, f4, trajR_R]
        have hf : brakeφ 4 = fun _ => 30 := by funext u; simp [brakeφ]
        rw [hf]; simpa [brakeφ] using hasDerivAt_const t (30:ℝ)
      · show HasDerivAt (brakeφ 5) _ t
        rw [show ((⟨5, by norm_num⟩ : Fin 6)) = (5 : Fin 6) from rfl, f5, trajR_R, trajR_R]
        have hf : brakeφ 5 = fun _ => 0 := by funext u; simp [brakeφ]
        rw [hf]; simpa [brakeφ] using hasDerivAt_const t (0:ℝ)
    · intro t ht ht1
      show Formula.sat domR _
      rw [sat_domR]
      simp only [Box, trajR_R]
      simp [brakeφ]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> nlinarith
  refine not_wellFormedR_of_run (Gr_modeAt 1 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 6 Side.R (mR 1)) xw
    rw [sat_guardR1]; simp [xw]; norm_num
  · show Formula.sat domR xw
    rw [sat_domR]; simp [Box, xw, Rv]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    have ht : e.tgt = 1 := by simp [edgeList] at hl; exact hl
    rw [ht] at hsat
    have := (sat_guardR1 _).mp hsat
    simp [trajR_R, brakeφ] at this
    linarith

/-- **`platoon3_linkloss` violates Assumption 1** (a model defect: the AEB sink `BRAKE1`
blocks; see the module docstring). -/
theorem platoon3_linkloss_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR platoon3_linkloss_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) platoon3_linkloss_brake1_blocks

end V2Platoon3Linkloss
end RelCertifier

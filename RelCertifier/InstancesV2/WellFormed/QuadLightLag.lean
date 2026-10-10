/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (one mode, `CLIMB`, with its self-loop),
the lowered right guard, `ε_r = 1`. `CLIMB` (`0 ≤ w ≤ 2.6`, `w' = 4 − w²`, `a' = 0`) has a
forward-invariant guard (style (a); barriers at both faces). Existence: the instance's
viability route (both `w` faces strict, `a` faces neutral), with the left held still, and a
time rescaling of the stretched run. Z3-free.
-/
import RelCertifier.InstancesV2.Modal.QuadLightLag
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightLag

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR quad_light_lag_IRv2 = 1 := by
  simp [epsR, quad_light_lag_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem sat_guardR0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ 0 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 13/5 := by
  simp [hostGuard, mR, quad_light_lag_IRv2, Run.lowerF, Run.lowerE, hp00, hp26, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- The instance's viability existence, with the left held still (`fL = 0`). -/
theorem es0 (dt : ℝ) (hdt : 0 ≤ dt) (σ : State (Var 2)) (hσ : Formula.sat domR σ) :
    HExistSegB (fun _ => Term.const 0) (fR 0) (Term.const (lam 0)) Formula.tt domR dt σ := by
  have hR := (sat_domR σ).mp hσ
  refine HExistSegB_of_viability_stratified (fun _ => Term.const 0) (fR 0)
    (Term.const (lam 0)) Formula.tt domR [faceLo, faceHi] [] [faceALo, faceAHi] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
      obtain ⟨j, hj⟩ := faces_fv gT (by simpa using hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fun _ => Term.const 0) _ hb
      obtain ⟨j, hj⟩ := facesA_fv gT hgT x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT hgT x _ hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_lo 0 0 (by norm_num) x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi 0 0 (by norm_num) x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x _ _
      have hi2 : i < 2 := by simpa using hi
      interval_cases i
      · have hfun : (fun ω : State (Var 2) => Term.eval ([faceALo, faceAHi][0]) ω)
            = fun y => (-1 : ℝ) * y (Rv 1) + 0 := by
          funext y
          simp [faceALo, Term.eval, AOp.interp]
        rw [hfun, hbndA 0 0 (by norm_num)]
      · have hfun : (fun ω : State (Var 2) => Term.eval ([faceALo, faceAHi][1]) ω)
            = fun y => (1 : ℝ) * y (Rv 1) + (-(149/20)) := by
          funext y
          simp [faceAHi, Term.eval, AOp.interp]
          ring
        rw [hfun, hbndA 0 0 (by norm_num)])
    (by
      intro x hS hN
      rw [sat_domR]
      obtain ⟨h0, h1⟩ := faces_val x (fun gT hgT => hS gT (by simpa using hgT))
      obtain ⟨h2, h3⟩ := facesA_val x hN
      exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩)
    16 43 1 one_pos
    (fun ν0 h0 => hLip 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd 0 0 (by norm_num) ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    dt hdt σ
    (by
      intro gT hgT
      rcases List.mem_cons.mp hgT with rfl | hgT
      · simp only [faceLo, Term.eval, AOp.interp]; linarith [hR.1.1.1]
      · rw [List.mem_singleton] at hgT
        subst hgT
        simp only [faceHi, Term.eval, AOp.interp]; linarith [hR.1.1.2])
    (by
      intro gT hgT
      rcases List.mem_cons.mp hgT with rfl | hgT
      · simp only [faceALo, Term.eval, AOp.interp]; linarith [hR.1.2]
      · rw [List.mem_singleton] at hgT
        subst hgT
        simp only [faceAHi, Term.eval, AOp.interp]; linarith [hR.2])
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-- **Assumption 1 for `quad_light_lag`** (style (a), Z3-free). -/
theorem quad_light_lag_wellFormedR : WellFormedR Gr guardR (epsR quad_light_lag_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq1, rfl⟩ := Gr_modeAt_inv hm
  obtain rfl : q = 0 := by omega
  have hgx := (sat_guardR0 x).mp hg
  refine ⟨?_, ?_⟩
  · obtain ⟨Φ, H⟩ := exists_of_HExistSegB_zero (lam_pos 0) (es0 (4/7) (by norm_num) x hd)
      (s := 4/7) (by norm_num) le_rfl
    rw [show (4/7 : ℝ) * lam 0 = 1 from by simp [lam]] at H
    exact ⟨Φ, H⟩
  · intro t Φ _ H
    have hf := fR0_eval 0 (by norm_num)
    have hup := H.coord_le_barrier 0 (13/5) (fun s _ hs => by
      rw [hf]; simp only [cRc]; nlinarith) hgx.2
    have hlo := H.coord_ge_barrier 0 0 (fun s hs hs0 => by
      have := ((sat_domR s).mp hs).1.1.1
      rw [hf]; simp only [cRc]; nlinarith) hgx.1
    exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR0 _).mpr ⟨hlo, hup⟩⟩

end V2QuadLightLag
end RelCertifier

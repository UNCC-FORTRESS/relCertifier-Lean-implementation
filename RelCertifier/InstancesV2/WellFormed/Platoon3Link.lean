/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The platoon3 link along the reference's own flow: the operating range is kept

Shared by `WellFormed/Platoon3Linkloss` and `WellFormed/Platoon3Profiles`. Along any run of a
damped link `x' = y`, `y' = −(1/8)(x − c) − (3/4) y` with `21 ≤ c ≤ 59` (the right
blocks' links), a start in the operating range's link conjuncts `x ≥ 20`,
`21 ≤ x + 2y ≤ 59` ends in them: the projected gap `x + 2y` is (twice) the slow form
`y + (x − c)/2`, which decays toward 0 (`boxle_Ronly_of_super` with `super_linear_ge_R` /
`super_linear_le_R`, root `1/2`), and the gap floor repels (`gap_floor_Ronly`). The rest of
the operating range (`x ≤ 60`, `|y| ≤ 10`) is the evolve box, which every run keeps.
Z3-free.
-/
import RelCertifier.InstancesV2.Modal.Platoon3Link
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace Platoon3Link

open DL DLCalTiming DLRel Set

/-- **The link's operating-range conjuncts are kept by the reference's own flow.** -/
theorem link_guard_Ronly (fR : Fin 6 → Term (Var 6)) (dom : Formula (Var 6)) (jx jy : Fin 6)
    (c : ℝ) (hc21 : 21 ≤ c) (hc59 : c ≤ 59) (hF : LinkField Rv fR jx jy c)
    {x : State (Var 6)} {t : ℝ} {Φ : ℝ → State (Var 6)}
    (H : ODESol (rightBlock fR (Term.const 1)) dom x t Φ)
    (hg : 20 ≤ x (Rv jx)) (hp1 : 21 ≤ x (Rv jx) + 2 * x (Rv jy))
    (hp2 : x (Rv jx) + 2 * x (Rv jy) ≤ 59) :
    20 ≤ Φ t (Rv jx) ∧ 21 ≤ Φ t (Rv jx) + 2 * Φ t (Rv jy) ∧
      Φ t (Rv jx) + 2 * Φ t (Rv jy) ≤ 59 := by
  have hs2 : (0:ℝ) ≤ 3/4 - 1/2 := by norm_num
  have hfv : ∀ (K : ℝ) (i : Fin 6), Lv i ∉ (linGe (Rv jx) (Rv jy) (1/2) c K).fv := by
    intro K i hi; simp [linGe, linQ, Term.fv, Lv, Rv] at hi
  have hfv' : ∀ (K : ℝ) (i : Fin 6), Lv i ∉ (linLe (Rv jx) (Rv jy) (1/2) c K).fv := by
    intro K i hi; simp [linLe, linQ, Term.fv, Lv, Rv] at hi
  refine ⟨?_, ?_, ?_⟩
  · refine gap_floor_Ronly fR dom jx jy c 20 21 (by norm_num) hc21 hF H.sem ?_ hg
    simp only [pgGe, Term.eval, AOp.interp]; linarith
  · have hbox := boxle_Ronly_of_super (linGe (Rv jx) (Rv jy) (1/2) c ((21 - c)/2)) fR 1
      zero_le_one dom dom (hfv _) (fun z hz => hz)
      (super_linear_ge_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z))
      (ν := x) (by simp only [linGe, eval_linQ, Term.eval, AOp.interp]; linarith)
    have := hbox (Φ t) H.sem
    simp only [linGe, eval_linQ, Term.eval, AOp.interp] at this
    linarith
  · have hbox := boxle_Ronly_of_super (linLe (Rv jx) (Rv jy) (1/2) c ((59 - c)/2)) fR 1
      zero_le_one dom dom (hfv' _) (fun z hz => hz)
      (super_linear_le_R (a := 1/8) (b := 3/4) hroot2 hs2 (by linarith) fR dom
        (fun z _ => hF.1 z) (fun z _ => hF.2 z))
      (ν := x) (by simp only [linLe, eval_linQ, Term.eval, AOp.interp]; linarith)
    have := hbox (Φ t) H.sem
    simp only [linLe, eval_linQ, Term.eval, AOp.interp] at this
    linarith

end Platoon3Link
end RelCertifier

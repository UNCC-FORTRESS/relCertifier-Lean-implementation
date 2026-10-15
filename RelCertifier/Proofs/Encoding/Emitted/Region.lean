/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# A region kept by the right flows is kept along joint segments

Assumption 1 relative to a region (`WellFormedRIn G guard reg ε` with `RegionInvariant G reg`,
the form the general theorem and the bridge are stated in; every generated instance takes
`reg = ⊤`): for the cover's
induction the region must also survive the joint segments, whose right part is the right flow
at the pairing's stretch. The right coordinates of a joint run `Φ` solve `ẏ = λ f_R(y)`
(`f_R` reads right coordinates only), so `u ↦ Φ(u/λ)`, merged over the start's left part, is a
solution of the unit-stretch right block over `λ·r`; `RegionInvariant` then keeps the region
(which reads right coordinates only) to the end.
-/
import RelCertifier.Proofs.Encoding.ReplayEngine
import RelCertifier.Proofs.Encoding.WellFormedR

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLCalTiming Set

variable {n : ℕ}

/-- The right projection of a joint run at stretch `c`, time-rescaled and merged over `σ`, is a
unit-stretch right-only solution. -/
theorem odeSol_right_of_joint {fL fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomR : domR.fv ⊆ range Rv) (c : ℝ) (hc : 0 < c)
    {σ ω : State (Var n)}
    (h : Program.sem (Program.ode (jointSys fL fR (Term.const c)) (Formula.and domL domR)) σ ω) :
    ∃ (r : ℝ) (Ψ : ℝ → State (Var n)),
      ODESol (rightBlock fR (Term.const 1)) domR (mergeLR σ σ σ) r Ψ ∧ Ψ r = mergeLR σ σ ω := by
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := h
  have hscale : ∀ u, 0 ≤ u → u ≤ c * r → u / c ∈ Icc (0:ℝ) r := by
    intro u hu0 hu2
    constructor
    · positivity
    · rw [div_le_iff₀ hc]; linarith
  refine ⟨c * r, fun u => mergeLR σ σ (Φ (u / c)), ⟨by positivity, by simp [hΦ0], ?_, ?_, ?_⟩, ?_⟩
  · -- derivatives: the right equations of the joint system, time-rescaled
    intro u hu p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hmem : ((Rv i : Var n), Term.binop .mul (Term.const c) (fR i)) ∈ jointSys fL fR (Term.const c) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    have hΦder := hder (u / c) (hscale u hu.1 hu.2) _ hmem
    have hσd : HasDerivWithinAt (fun v : ℝ => v / c) (1 / c) (Icc 0 (c * r)) u := by
      have hda : HasDerivAt (fun v : ℝ => v / c) (1 / c) u := by
        simpa using (hasDerivAt_id u).div_const c
      exact hda.hasDerivWithinAt
    have hmaps : MapsTo (fun v : ℝ => v / c) (Icc 0 (c * r)) (Icc 0 r) :=
      fun v hv => hscale v hv.1 hv.2
    have hcomp := HasDerivWithinAt.scomp u hΦder hσd hmaps
    have hval : Term.eval (Term.binop .mul (Term.const 1) (fR i)) (mergeLR σ σ (Φ (u / c)))
        = (1 / c) * Term.eval (Term.binop .mul (Term.const c) (fR i)) (Φ (u / c)) := by
      have hag : Term.eval (fR i) (mergeLR σ σ (Φ (u / c))) = Term.eval (fR i) (Φ (u / c)) := by
        refine Term.coincidence _ (fun v hv => ?_)
        obtain ⟨j, rfl⟩ := hfR i hv
        exact mergeLR_R σ _ _ j
      simp only [Term.eval, AOp.interp, hag]
      field_simp
    have hf : (fun v => mergeLR σ σ (Φ (v / c)) (Rv i)) = (fun s => Φ s (Rv i)) ∘ fun v => v / c := by
      funext v; exact mergeLR_R σ _ _ i
    show HasDerivWithinAt (fun v => mergeLR σ σ (Φ (v / c)) (Rv i)) _ _ u
    rw [hval, hf]
    exact hcomp
  · -- mask: only right coordinates move
    intro u _ v hv
    obtain ⟨sd, i⟩ := v
    cases sd with
    | L => simp [mergeLR]
    | R =>
        exfalso; apply hv
        simp only [rightBlock, ODESystem.bound, List.map_map, List.mem_map, List.mem_finRange,
          true_and]
        exact ⟨i, rfl⟩
    | Aux => simp [mergeLR]
  · -- domain: the right envelope, read on the right coordinates
    intro u hu
    refine (Formula.coincidence domR (fun v hv => ?_)).mpr (hdom (u / c) (hscale u hu.1 hu.2)).2
    obtain ⟨j, rfl⟩ := hdomR hv
    exact mergeLR_R σ _ _ j
  · show mergeLR σ σ (Φ (c * r / c)) = mergeLR σ σ ω
    rw [show c * r / c = r from by field_simp, hΦr]

/-- A right-only region kept by every right flow (`RegionInvariant`) is kept along a joint
segment at any positive stretch. -/
theorem reg_kept_joint {G : SearchGraph (Var n)} {reg : Formula (Var n)}
    (hinv : RegionInvariant G reg) (hregR : reg.fv ⊆ range Rv)
    {fL fR : Fin n → Term (Var n)} {domL domR : Formula (Var n)}
    (hfR : ∀ i, (fR i).fv ⊆ range Rv) (hdomR : domR.fv ⊆ range Rv)
    {q : ℕ} {m : RMode (Var n)} (hm : G.modeAt q = some m)
    (hsys : m.sys = rightBlock fR (Term.const 1)) (hdomM : m.dom = domR)
    (c : ℝ) (hc : 0 < c) {σ ω : State (Var n)}
    (h : Program.sem (Program.ode (jointSys fL fR (Term.const c)) (Formula.and domL domR)) σ ω)
    (hσ : Formula.sat reg σ) : Formula.sat reg ω := by
  obtain ⟨r, Ψ, H, hend⟩ := odeSol_right_of_joint hfR hdomR c hc h
  have hσ' : Formula.sat reg (mergeLR σ σ σ) := by
    refine (Formula.coincidence reg (fun v hv => ?_)).mpr hσ
    obtain ⟨j, rfl⟩ := hregR hv
    exact mergeLR_R σ σ σ j
  have hH : ODESol m.sys m.dom (mergeLR σ σ σ) r Ψ := by rw [hsys, hdomM]; exact H
  have := hinv q m hm _ r Ψ hσ' hH
  rw [hend] at this
  refine (Formula.coincidence reg (fun v hv => ?_)).mp this
  obtain ⟨j, rfl⟩ := hregR hv
  exact mergeLR_R σ _ _ j

end Emitted
end RelCertifier

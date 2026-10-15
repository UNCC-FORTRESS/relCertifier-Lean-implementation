/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 8: Theorem 3 in the window form, for one declared row

When every left mode declares the same row (`rowsSame`), the per-window loop of
`theorem3_of_coverX` applies directly: the guard-gated windows of the left modes, the guarded
right automaton, the row with the envelope and the right region. Two auxiliary coordinates
suffice (the right mode variable and the window clock).
-/
import RelCertifier.Proofs.Encoding.Emitted.Keyed

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL DLRel DLCalTiming Parse Run Set Oracle Progress

variable {n : ℕ}

/-- Every declared row is the first one. -/
def rowsSame (p : PProblem) : Bool :=
  p.invariants.all (fun kv => kv.2 == (p.invariants.getD 0 ("", PForm.tt)).2)

theorem rowOf_same {p : PProblem} (h : rowsSame p = true) (l : ℕ) : rowOf p l = rowOf p 0 := by
  simp only [rowsSame, List.all_eq_true, beq_iff_eq] at h
  unfold rowOf rowIdx
  by_cases hl : p.invariants.length > l
  · rw [if_pos hl]
    have hmem : p.invariants.getD l ("", PForm.tt) ∈ p.invariants := by
      rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
    rw [h _ hmem]
    by_cases h0 : p.invariants.length > 0
    · rw [if_pos h0]
    · rw [if_neg h0]
  · rw [if_neg hl]
    by_cases h0 : p.invariants.length > 0
    · rw [if_pos h0]
    · rw [if_neg h0]

theorem FRow_same {p : PProblem} (h : rowsSame p = true) (l : ℕ) :
    FRow p n l = FRow p n 0 := by
  unfold FRow g gs comps; rw [rowOf_same h]

/-- The claim of a one-row benchmark: Theorem 3 over the guard-gated windows and the guarded
right automaton, loop invariant the row with the envelope and the right region. -/
def windowClaim (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (a b : Fin n) (dt : ℝ) : Prop :=
  RFormula.rvalid (theorem3Form
    (bigChoice (leftProgsOf b dt (domL p n) (nL p) (guardL p n) (fL p n)))
    (rightAutomatonBody (grOf p n (prunedOf cov)) ((Side.Aux, a) : Var n))
    (RFormula.and (RFormula.and (canonInvM (g p n 0) (gs p n 0)) (envLR (domL p n) (domR p n)))
      (mvRegionR ((Side.Aux, a) : Var n) (regionG (guardR p n) (cuts p n cX))
        (grOf p n (prunedOf cov)).modes.length)))

section Proofs

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE} {prog : ProgressEmitE}
  (hs : structOK p n cov cX = true)

include hs

/-- The anchor at an admissible start of any right index (out of range its right atoms and
barriers are empty). -/
theorem AG_start_any (hnc : NonConnAll p n cX cov) {l : ℕ} (hl : l < nL p) (q : ℕ)
    (σ : State (Var n)) (hgL : Formula.sat (guardL p n l) σ)
    (hσ : Formula.sat (Formula.and (FRow p n l) (env p n)) σ)
    (hg : Formula.sat (guardR p n q) σ) (hc : Formula.sat (cuts p n cX q) σ) :
    Formula.sat (AG p n cX cov l q) σ := by
  by_cases hq : q < nR p
  · exact AG_start hs hnc hl hq σ hgL hσ hg hc
  refine ⟨(sat_FM_append _ _ _ σ).mpr ⟨(sat_FM_append _ _ _ σ).mpr ⟨hσ.1, ?_⟩, ?_⟩, hσ.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR_any hs q) σ).mpr
      ⟨cutsL_of_guard hs hl σ hgL, (sat_cutF _ _).mp hc⟩
  · rw [barriers_dm hq]; simp

/-- **Theorem 3 of a benchmark with one declared row, from its records.** -/
theorem theorem3_window_of_records (hv : Verdicts p n cX cov prog)
    (hpo : progOK p n cov prog = true) (hcovers : coversOK p n cov = true)
    (hwf : WellFormedR (grOf p n (prunedOf cov)) (guardR p n) (epsR p))
    (hsame : rowsSame p = true) (a b : Fin n) (hab : a ≠ b) (dt : ℝ) (hdt : dt ≤ epsL p) :
    windowClaim p n cX cov a b dt := by
  unfold windowClaim
  refine theorem3_of_coverX (grOf p n (prunedOf cov)) a b hab dt (g p n 0) (gs p n 0)
    (comps_fv_any (p := p) (n := n) 0) (domL p n) (domR p n) (domL_fv (hnames hs))
    (domR_fv (hnames hs)) (guardR p n) (cuts p n cX) grOf_guards (grOf_guardsRight (hnames hs))
    (guardR_fv (hnames hs)) (cuts_fv hs) (fR p n) (fun q _ => fR_fv (hnames hs) q)
    (fun _ _ hm => grOf_sys hm) (fun _ _ hm => grOf_dom hm) (fun _ _ hm => grOf_weight hm)
    (grOf_lt (n := n) (hres hs)) (nL p) (guardL p n) (fL p n) (fun l _ => guardL_fv (hnames hs) l)
    (fun l _ => fL_fv (hnames hs) l) (epsR p) hwf (chOf p cov) (B p cov) (δ p cov) (lamOf p cov)
    (AG p n cX cov) (fun _ _ => Formula.tt) (fun _ _ _ => Formula.tt)
    (fun l q _ => Formula.and (AG p n cX cov l q) (guardR p n q))
    (fun l hl => coverHyps_of hs hv hpo hwf hl) (fun l hl => hdt.trans (budget_span hs hl))
    ?_ ?_ ?_
  · intro l hl q hq hadm
    refine hcov_of hs hv hcovers hl q hq ?_
    obtain ⟨σ, h1, h2, h3, h4⟩ := hadm
    refine ⟨σ, h1, ⟨?_, h2.2⟩, h3, h4⟩
    show Formula.sat (FRow p n l) σ
    rw [FRow_same hsame]; exact h2.1
  · intro l hl q σ hgL hσ hg hc
    refine AG_start_any hs hv.nonconn hl q σ hgL ⟨?_, hσ.2⟩ hg hc
    show Formula.sat (FRow p n l) σ
    rw [FRow_same hsame]; exact hσ.1
  · intro l hl q' y hA
    have := AG_post_any hs hl q' y hA
    refine ⟨⟨?_, this.1.2⟩, this.2⟩
    have hF : Formula.sat (FRow p n l) y := this.1.1
    rw [FRow_same hsame] at hF; exact hF

end Proofs

end Emitted
end RelCertifier

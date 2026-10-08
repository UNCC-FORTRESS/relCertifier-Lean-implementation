/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_b_12dof` — the DECLARED mode-dependent invariant, composed

`Story1AttdistRungBModal.story1_attdist_rung_b_modal` states Theorem 3 at the STEEP row's
first two components (`v[l] ≤ v[r]` and the ψ energy) for every left window, region-
conditioned by each right mode's checked-cut ceiling `v_R ≤ c_m` (the L4 chain). The file
declares `STEEP = v[l] ≤ v[r] ∧ D_ψ ∧ D_θ` and `MODER = FLAT = D_ψ ∧ D_θ`. This leaf states
that: one row per LEFT mode, keyed by `u_L = (Aux, 2)`, as a ∀∃ invariant of the left
automaton over the file's `next` lists, with the same region bookkeeping. Ingredients:

* per row `r` a verdict pack `VerdR r m` (ceiling face first, then the row's components,
  against right mode `m`), the base instance's coupling and climb-to-`max(l, q)` response
  re-instantiated at that row (`coupleR`, `respondR`, `HmultiR` are the base `coupleF`,
  `respondF`, `HmultiF` with the row's list in place of `[v, ψ]`);
* the base existence lemma `esF` with its invariant hypothesis weakened to the two facts
  it reads — the ceiling and the right envelope (`esFG`; the body is `esF`'s, verbatim),
  so the MODER/FLAT rows, which carry no `v` conjunct, can use it;
* the handoffs, in-kernel: `STEEP → MODER` drops the `v` conjunct, `MODER → FLAT` is an
  identical row, self-loops are trivial.

Residuals: six packs — `VerdR 0 m` (4 queries each, `m < 3`), `VerdR 1 1`, `VerdR 1 2`,
`VerdR 2 2` (3 queries each) — every one re-run by `relcert --run-verdicts` and pinned to
the runner's query in `Verdicts/ModalPinTable.lean`.
-/
import RelCertifier.Instances.Story1AttdistRungBModal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace Story1AttdistRungBHandoff

open DL DLCalTiming DLRel Parse Set Story1AttdistRungBModal

set_option maxHeartbeats 12800000

/-- The left mode variable — the third auxiliary (`mv = (Aux, 0)`, `tg = (Aux, 1)`). -/
abbrev ulF : Var 12 := (Side.Aux, 2)

/-- The right modes' checked-cut ceilings (the base instance's `cstF`). -/
noncomputable def cst (m : ℕ) : ℝ := if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20

/-! ## The declared rows -/

def invRowPF (r : ℕ) : Parse.PForm :=
  (story1_attdist_rung_b_12dof_IR.invariants.getD r ("", Parse.PForm.tt)).2

noncomputable def gRowAt (r i : ℕ) : Term (Var 12) :=
  ((Run.invToG vsF 12 ((atomsOf (invRowPF r)).getD i .tt)).map ITerm.toHost).getD (Term.const 0)

/-- Row `r`'s head component and its tail: STEEP has three components, the others two. -/
noncomputable def gR (r : ℕ) : Term (Var 12) := gRowAt r 0
noncomputable def gsR : ℕ → List (Term (Var 12))
  | 0 => [gRowAt 0 1, gRowAt 0 2]
  | r => [gRowAt r 1]

noncomputable def FRow (r : ℕ) : Formula (Var 12) := FM (gR r) (gsR r)
noncomputable def ϕRow (r : ℕ) : RFormula (Var 12) := canonInvM (gR r) (gsR r)

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 12)) (ϕRow r) = FRow r :=
  encode_canonInvM _ _

/-- The row enriched with right mode `m`'s ceiling (the region face), as the coupling sees it. -/
noncomputable def gs9R (r m : ℕ) : List (Term (Var 12)) := gsR r ++ [ceilF m]

/-- STEEP's first two components are the base instance's `gF`, `gAt 1` (same row). -/
theorem gR_zero : gR 0 = gF := rfl
theorem gRowAt_zero_one : gRowAt 0 1 = gAt 1 := rfl

/-- The MODER and FLAT rows are STEEP's last two components, term for term. -/
theorem atoms_one_zero : (atomsOf (invRowPF 1)).getD 0 .tt = (atomsOf invFPF).getD 1 .tt := by
  decide
theorem atoms_one_one : (atomsOf (invRowPF 1)).getD 1 .tt = (atomsOf invFPF).getD 2 .tt := by
  decide
theorem atoms_two_zero : (atomsOf (invRowPF 2)).getD 0 .tt = (atomsOf invFPF).getD 1 .tt := by
  decide
theorem atoms_two_one : (atomsOf (invRowPF 2)).getD 1 .tt = (atomsOf invFPF).getD 2 .tt := by
  decide
theorem gRowAt_one_zero : gRowAt 1 0 = gRowAt 0 1 := by
  unfold gRowAt; rw [atoms_one_zero]; rfl
theorem gRowAt_one_one : gRowAt 1 1 = gRowAt 0 2 := by
  unfold gRowAt; rw [atoms_one_one]; rfl
theorem gRowAt_two_zero : gRowAt 2 0 = gRowAt 0 1 := by
  unfold gRowAt; rw [atoms_two_zero]; rfl
theorem gRowAt_two_one : gRowAt 2 1 = gRowAt 0 2 := by
  unfold gRowAt; rw [atoms_two_one]; rfl

theorem FRow_two_eq_one : FRow 2 = FRow 1 := by
  show FM (gRowAt 2 0) [gRowAt 2 1] = FM (gRowAt 1 0) [gRowAt 1 1]
  rw [gRowAt_two_zero, gRowAt_two_one, gRowAt_one_zero, gRowAt_one_one]

theorem hgRowAt (r i : ℕ) : (gRowAt r i).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem aux_notin_gRowAt (a : Fin 12) (r i : ℕ) : ((Side.Aux, a) : Var 12) ∉ (gRowAt r i).fv := by
  intro h
  rcases hgRowAt r i h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem mem_gsR {r : ℕ} {g : Term (Var 12)} (hg : g ∈ gR r :: gsR r) : ∃ i, g = gRowAt r i := by
  cases r with
  | zero =>
      simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  | succ r =>
      simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem aux_notin_FRow (a : Fin 12) (r : ℕ) : ((Side.Aux, a) : Var 12) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' => by
    obtain ⟨i, rfl⟩ := mem_gsR hg'
    exact aux_notin_gRowAt a r i)

theorem aux_notin_gs9R (a : Fin 12) (r m : ℕ) :
    ∀ g' ∈ gR r :: gs9R r m, ((Side.Aux, a) : Var 12) ∉ g'.fv := by
  intro g' hg' h
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact aux_notin_gRowAt a r 0 h
  · rcases List.mem_append.mp hg' with hg' | hg'
    · obtain ⟨i, rfl⟩ := mem_gsR (List.mem_cons_of_mem _ hg')
      exact aux_notin_gRowAt a r i h
    · rw [List.mem_singleton] at hg'
      subst hg'
      exact absurd (ceilF_fv m h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem htgF9R (r m : ℕ) : tgF ∉ (FM (gR r) (gs9R r m)).fv :=
  notMem_FM_fv (aux_notin_gs9R 1 r m)

theorem FM_drop9R (r m : ℕ) {ν : State (Var 12)}
    (h : Formula.sat (FM (gR r) (gs9R r m)) ν) : Formula.sat (FRow r) ν := by
  refine FM_mono ?_ h
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hg)

theorem FM_add9R (r m : ℕ) {ν : State (Var 12)}
    (h : Formula.sat (FRow r) ν) (hb : ν (Rv 0) ≤ cst m) :
    Formula.sat (FM (gR r) (gs9R r m)) ν := by
  rw [FRow, sat_FM_iff] at h
  rw [sat_FM_iff]
  intro g' hg'
  rcases List.mem_cons.mp hg' with rfl | hg'
  · exact h _ List.mem_cons_self
  · rcases List.mem_append.mp hg' with hg' | hg'
    · exact h g' (List.mem_cons_of_mem _ hg')
    · rw [List.mem_singleton] at hg'
      subst hg'
      simp only [ceilF, Term.eval, AOp.interp, cst] at hb ⊢
      linarith

theorem ceil_of_FM9R (r m : ℕ) {ν : State (Var 12)}
    (h : Formula.sat (FM (gR r) (gs9R r m)) ν) : ν (Rv 0) ≤ cst m := by
  have := (sat_FM_iff _ _ ν).mp h (ceilF m)
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  simp only [ceilF, Term.eval, AOp.interp, cst] at this ⊢
  linarith

/-! ## Existence, from the two facts the base lemma reads

`esF`'s body, verbatim, with the invariant hypothesis replaced by the ceiling and the
right envelope — the only two things it used it for. -/

theorem esFG (l m : ℕ) (hl : l < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ σ, σ (Rv 0) ≤ (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20) →
      Formula.sat domRF σ →
      HExistSegB (fLF l) (fRF m) (Term.const (1)) domLF domRF dt
        (Function.update σ tgF 0) := by
  intro σ hceil hR
  rw [sat_domRF] at hR
  obtain ⟨hd9l, hd9h, hd3l, hd3h, hd5l, hd5h, hd11l, hd11h, hd7l, hd7h, hd8l, hd8h, hd2l, hd2h, hd1l, hd4l, hd4h, hd0l, hd0h, hd10l, hd10h, hd6l, hd6h⟩ := hR
  have hupd : ∀ j : Fin 12, σ (Side.R, j) = Function.update σ tgF 0 (Side.R, j) := by
    intro j
    rw [Function.update_of_ne (by simp [tgF, Prod.ext_iff])]
  have hfS : ∀ gT' ∈ gsSF, Term.eval gT' (Function.update σ tgF 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsSF, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceVLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceVHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPsHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOThHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceYHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsAuxLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [facePsAuxHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThAuxLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceThAuxHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  have hfN : ∀ gT' ∈ gsNF, Term.eval gT' (Function.update σ tgF 0) ≤ 0 := by
    intro gT' hgT
    simp only [gsNF, List.mem_cons, List.not_mem_nil, or_false] at hgT
    rcases hgT with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · first
          | (simp only [faceSLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOZLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOZHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOPhHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOYLo, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
          | (simp only [faceOYHi, Term.eval, AOp.interp, Rv]; rw [← hupd]; linarith)
  refine HExistSegB_of_viability_stratA (fLF l) (fRF m) (Term.const (1))
    domLF domRF gsSF [] gsNF 0 le_rfl
    [((Rv 0 : Var 12), (3:ℝ),
      (3) * (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20),
      (if m = 0 then (3:ℝ)/10 else if m = 1 then 1/2 else 13/20)),
     ((Rv 2 : Var 12), 1, (3:ℝ)/5, (3:ℝ)/5),
     ((Rv 4 : Var 12), 1, (3:ℝ)/5, (3:ℝ)/5)]
    [((Rv 2 : Var 12), 1, -(3:ℝ)/5, -(3:ℝ)/5),
     ((Rv 4 : Var 12), 1, -(3:ℝ)/5, -(3:ℝ)/5)]
    (jointSys_wellFormed _ _ _)
    (by
      intro gT' hgT x hxf hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RF gT' (by
        rcases List.mem_append.mp hgT with h | h
        · exact List.mem_append_left _ h
        · exact absurd h (List.not_mem_nil)) x hxf
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro gT' hgT x hxf hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ hb
      obtain ⟨j, hj⟩ := faces_fv_RF gT' (List.mem_append_right _ hgT) x hxf
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ hb
      rcases hp with rfl | rfl | rfl <;>
        exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF l) _ hb
      rcases hp with rfl | rfl <;>
        exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · show (3:ℝ) * (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20)
          ≤ (3:ℝ) * (if m = 0 then (3:ℝ)/10 else if m = 1 then 1/2 else 13/20)
        split_ifs <;> norm_num
      · norm_num
      · norm_num)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> norm_num)
    (by
      intro gT' hgT x hsub hface
      exact hbndS_F m hm gT' hgT x hsub hface)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro i hi x hxs _
      exact hbndN_F m hm i hi x hxs)
    (by
      intro p hp x hxs _
      have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      have hops2 : x (Rv 3) ≤ (3:ℝ)/5 := by
        have := hxs faceOPsHi (List.mem_append_left _ (by simp [gsSF]))
        simp only [faceOPsHi, Term.eval, AOp.interp] at this; linarith
      have hoth2 : x (Rv 5) ≤ (3:ℝ)/5 := by
        have := hxs faceOThHi (List.mem_append_left _ (by simp [gsSF]))
        simp only [faceOThHi, Term.eval, AOp.interp] at this; linarith
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rw [odeField_RF m hm]
        simp only [eq_self_iff_true, if_true, if_pos rfl]
        show (3 * (cstF m - x (Rv 0)))
          ≤ (3:ℝ) * (if m = 0 then 3/10 else if m = 1 then 1/2 else 13/20)
            - (3:ℝ) * x (Rv 0)
        simp only [cstF]
        split_ifs <;> ring_nf <;> norm_num
      · rw [odeField_RF m hm]
        simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
          eq_self_iff_true, if_true, if_pos rfl]
        show (x (Rv 3) - x (Rv 2)) ≤ (3:ℝ)/5 - 1 * x (Rv 2)
        nlinarith [hops2]
      · rw [odeField_RF m hm]
        simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
          if_neg (hne 4 2 (by decide)), if_neg (hne 4 3 (by decide)),
          eq_self_iff_true, if_true, if_pos rfl]
        show (x (Rv 5) - x (Rv 4)) ≤ (3:ℝ)/5 - 1 * x (Rv 4)
        nlinarith [hoth2])
    (by
      intro p hp x hxs _
      have hne : ∀ (a b : Fin 12), a ≠ b → (Rv a : Var 12) ≠ Rv b := by
        intro a b hab
        simp [Rv, Prod.ext_iff]
        exact fun h => hab (by exact_mod_cast h)
      have hops1 : -(3:ℝ)/5 ≤ x (Rv 3) := by
        have := hxs faceOPsLo (List.mem_append_left _ (by simp [gsSF]))
        simp only [faceOPsLo, Term.eval, AOp.interp] at this; linarith
      have hoth1 : -(3:ℝ)/5 ≤ x (Rv 5) := by
        have := hxs faceOThLo (List.mem_append_left _ (by simp [gsSF]))
        simp only [faceOThLo, Term.eval, AOp.interp] at this; linarith
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [odeField_RF m hm]
        simp only [if_neg (hne 2 0 (by decide)), if_neg (hne 2 1 (by decide)),
          eq_self_iff_true, if_true, if_pos rfl]
        show -(3:ℝ)/5 - 1 * x (Rv 2) ≤ (x (Rv 3) - x (Rv 2))
        nlinarith [hops1]
      · rw [odeField_RF m hm]
        simp only [if_neg (hne 4 0 (by decide)), if_neg (hne 4 1 (by decide)),
          if_neg (hne 4 2 (by decide)), if_neg (hne 4 3 (by decide)),
          eq_self_iff_true, if_true, if_pos rfl]
        show -(3:ℝ)/5 - 1 * x (Rv 4) ≤ (x (Rv 5) - x (Rv 4))
        nlinarith [hoth1])
    (by
      intro x hS hN hAU hAL
      have hS' : ∀ gT' ∈ gsSF, Term.eval gT' x ≤ 0 :=
        fun gT' hgT => hS gT' (List.mem_append_left _ hgT)
      have hb0l : 0 ≤ x (Rv 0) := by
        have := hS' faceVLo (by simp [gsSF])
        simp only [faceVLo, Term.eval, AOp.interp] at this; linarith
      have hb0h : x (Rv 0) ≤ (4:ℝ)/5 := by
        have := hS' faceVHi (by simp [gsSF])
        simp only [faceVHi, Term.eval, AOp.interp] at this; linarith
      have hb3l : -(3:ℝ)/5 ≤ x (Rv 3) := by
        have := hS' faceOPsLo (by simp [gsSF])
        simp only [faceOPsLo, Term.eval, AOp.interp] at this; linarith
      have hb3h : x (Rv 3) ≤ (3:ℝ)/5 := by
        have := hS' faceOPsHi (by simp [gsSF])
        simp only [faceOPsHi, Term.eval, AOp.interp] at this; linarith
      have hb5l : -(3:ℝ)/5 ≤ x (Rv 5) := by
        have := hS' faceOThLo (by simp [gsSF])
        simp only [faceOThLo, Term.eval, AOp.interp] at this; linarith
      have hb5h : x (Rv 5) ≤ (3:ℝ)/5 := by
        have := hS' faceOThHi (by simp [gsSF])
        simp only [faceOThHi, Term.eval, AOp.interp] at this; linarith
      have hb6l : -(1:ℝ) ≤ x (Rv 6) := by
        have := hS' faceZLo (by simp [gsSF])
        simp only [faceZLo, Term.eval, AOp.interp] at this; linarith
      have hb6h : x (Rv 6) ≤ (3:ℝ)/20 := by
        have := hS' faceZHi (by simp [gsSF])
        simp only [faceZHi, Term.eval, AOp.interp] at this; linarith
      have hb8l : -(1:ℝ)/2 ≤ x (Rv 8) := by
        have := hS' facePhLo (by simp [gsSF])
        simp only [facePhLo, Term.eval, AOp.interp] at this; linarith
      have hb8h : x (Rv 8) ≤ (3:ℝ)/20 := by
        have := hS' facePhHi (by simp [gsSF])
        simp only [facePhHi, Term.eval, AOp.interp] at this; linarith
      have hb10l : -(1:ℝ)/2 ≤ x (Rv 10) := by
        have := hS' faceYLo (by simp [gsSF])
        simp only [faceYLo, Term.eval, AOp.interp] at this; linarith
      have hb10h : x (Rv 10) ≤ (3:ℝ)/20 := by
        have := hS' faceYHi (by simp [gsSF])
        simp only [faceYHi, Term.eval, AOp.interp] at this; linarith
      have hb2l : -(2:ℝ) ≤ x (Rv 2) := by
        have := hS' facePsAuxLo (by simp [gsSF])
        simp only [facePsAuxLo, Term.eval, AOp.interp] at this; linarith
      have hb2h : x (Rv 2) ≤ (2:ℝ) := by
        have := hS' facePsAuxHi (by simp [gsSF])
        simp only [facePsAuxHi, Term.eval, AOp.interp] at this; linarith
      have hb4l : -(2:ℝ) ≤ x (Rv 4) := by
        have := hS' faceThAuxLo (by simp [gsSF])
        simp only [faceThAuxLo, Term.eval, AOp.interp] at this; linarith
      have hb4h : x (Rv 4) ≤ (2:ℝ) := by
        have := hS' faceThAuxHi (by simp [gsSF])
        simp only [faceThAuxHi, Term.eval, AOp.interp] at this; linarith
      have hb1l : 0 ≤ x (Rv 1) := by
        have := hN faceSLo (by simp [gsNF])
        simp only [faceSLo, Term.eval, AOp.interp] at this; linarith
      have hb7l : -(2:ℝ)/5 ≤ x (Rv 7) := by
        have := hN faceOZLo (by simp [gsNF])
        simp only [faceOZLo, Term.eval, AOp.interp] at this; linarith
      have hb7h : x (Rv 7) ≤ (1:ℝ)/2 := by
        have := hN faceOZHi (by simp [gsNF])
        simp only [faceOZHi, Term.eval, AOp.interp] at this; linarith
      have hb9l : -(2:ℝ)/5 ≤ x (Rv 9) := by
        have := hN faceOPhLo (by simp [gsNF])
        simp only [faceOPhLo, Term.eval, AOp.interp] at this; linarith
      have hb9h : x (Rv 9) ≤ (1:ℝ)/2 := by
        have := hN faceOPhHi (by simp [gsNF])
        simp only [faceOPhHi, Term.eval, AOp.interp] at this; linarith
      have hb11l : -(2:ℝ)/5 ≤ x (Rv 11) := by
        have := hN faceOYLo (by simp [gsNF])
        simp only [faceOYLo, Term.eval, AOp.interp] at this; linarith
      have hb11h : x (Rv 11) ≤ (1:ℝ)/2 := by
        have := hN faceOYHi (by simp [gsNF])
        simp only [faceOYHi, Term.eval, AOp.interp] at this; linarith
      have ha2h : x (Rv 2) ≤ (3:ℝ)/5 := by
        have := hAU ((Rv 2 : Var 12), 1, (3:ℝ)/5, (3:ℝ)/5) (by simp)
        simpa using this
      have ha2l : -(3:ℝ)/5 ≤ x (Rv 2) := by
        have := hAL ((Rv 2 : Var 12), 1, -(3:ℝ)/5, -(3:ℝ)/5) (by simp)
        simpa using this
      have ha4h : x (Rv 4) ≤ (3:ℝ)/5 := by
        have := hAU ((Rv 4 : Var 12), 1, (3:ℝ)/5, (3:ℝ)/5) (by simp)
        simpa using this
      have ha4l : -(3:ℝ)/5 ≤ x (Rv 4) := by
        have := hAL ((Rv 4 : Var 12), 1, -(3:ℝ)/5, -(3:ℝ)/5) (by simp)
        simpa using this
      exact (sat_domRF x).mpr ⟨hb9l, hb9h, hb3l, hb3h, hb5l, hb5h, hb11l, hb11h, hb7l, hb7h, hb8l, hb8h, ha2l, ha2h, hb1l, ha4l, ha4h, hb0l, hb0h, hb10l, hb10h, hb6l, hb6h⟩)
    60 60 1 one_pos
    (fun ν0 h0 => hLip_F m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    (fun ν0 h0 => hfbnd_F m hm ν0 (fun gT hgT => h0 gT (List.mem_append_left _ hgT)))
    dt hdt
    (Function.update σ tgF 0)
    hfS
    hfN
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · show Function.update σ tgF 0 (Rv 0)
          ≤ (if m = 0 then (3:ℝ)/10 else if m = 1 then 1/2 else 13/20)
        rw [← hupd 0]
        exact hceil
      · show Function.update σ tgF 0 (Rv 2) ≤ (3:ℝ)/5
        rw [← hupd 2]
        linarith
      · show Function.update σ tgF 0 (Rv 4) ≤ (3:ℝ)/5
        rw [← hupd 4]
        linarith)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · show -(3:ℝ)/5 ≤ Function.update σ tgF 0 (Rv 2)
        rw [← hupd 2]
        linarith
      · show -(3:ℝ)/5 ≤ Function.update σ tgF 0 (Rv 4)
        rw [← hupd 4]
        linarith)
    (by intro gT' hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The per-row verdict packs, coupling and response -/

/-- Row `r`'s pack against right mode `m`: the ceiling face first, then the row's
components in order, at λ = 1. -/
def VerdR (r m : ℕ) : Prop :=
  ∀ i (hi : i < (ceilF m :: gR r :: gsR r).length),
    z3solve (flowQuery ⟨(ceilF m :: gR r :: gsR r)[i], fLF r, fRF m, Term.const (1),
      strataDomHost (Formula.and domLF domRF) ((ceilF m :: gR r :: gsR r).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQueryStrict ⟨(ceilF m :: gR r :: gsR r)[i], fLF r, fRF m, Term.const (1),
      strataDomHost (Formula.and domLF domRF) ((ceilF m :: gR r :: gsR r).take i)⟩) = Verdict.unsat
    ∨ z3solve (flowQuerySuperlevel ⟨(ceilF m :: gR r :: gsR r)[i], fLF r, fRF m, Term.const (1),
      strataDomHost (Formula.and domLF domRF) ((ceilF m :: gR r :: gsR r).take i)⟩) = Verdict.unsat

theorem coupleR (r m : ℕ) (hr : r < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdR r m) :
    ∀ σ', Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF) σ' → σ' tgF = 0 →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF r))) domLF)
        (Program.ode (rightBlock (fRF m) (Term.const (1))) domRF)
        (Formula.and (FM (gR r) (gs9R r m)) envF) tgF dt σ' := by
  intro σ' hσ' htg0
  have hupd : Function.update σ' tgF (0 : ℝ) = σ' := by
    funext x
    by_cases hx : x = tgF
    · subst hx; rw [Function.update_self]; exact htg0.symm
    · rw [Function.update_of_ne hx]
  have hAll := segPresAll_from_strata_verdicts' (fLF r) (fRF m) (Term.const (1))
    (Formula.and domLF domRF) (ceilF m :: gR r :: gsR r) hv
  have hmemV : ∀ g' ∈ gR r :: gs9R r m, g' ∈ ceilF m :: gR r :: gsR r := by
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg')
      · rw [List.mem_singleton] at hg'
        subst hg'
        exact List.mem_cons_self
  have hboxes : ∀ g' ∈ gR r :: gs9R r m, Formula.sat (Formula.box (Program.ode
      (leftBlock (fLF r) ++ rightBlock (fRF m) (Term.const (1)))
      (Formula.and domLF domRF)) (invLe g')) σ' := by
    intro g' hg'
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    refine hAll σ' ?_ ω (by rw [← jointSys_split] at hω; exact hω) g' (hmemV g' hg')
    intro g hg
    have hgmem : g ∈ gR r :: gs9R r m := by
      rcases List.mem_cons.mp hg with rfl | hg
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hg)
    exact (sat_FM_iff (gR r) (gs9R r m) σ').mp hσ'.1 g hgmem
  have hbase := segment_faModalB_from_certB_list (gR r) (gs9R r m) (fLF r) (fRF m)
    (Term.const (1)) domLF domRF tgF dt
    (LR_blocks_disjoint _ _ _ (hfLF r hr) (hfRF m hm) (by simp [Term.fv]))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomLF hv'
      exact Lv_mem_leftBlock_boundSet _ i))
    (fun v hv' => Or.inl (by
      obtain ⟨i, rfl⟩ := hdomRF hv'
      exact Rv_mem_rightBlock_boundSet _ _ i))
    (fun h => by
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF r) _ h
      exact aux_ne_Lv aF i hi)
    (fun h => aux_notin_range_Lv aF (leftBlock_readVars_sub (fLF r) (hfLF r hr) h))
    (fun h => by
      obtain ⟨i, hi⟩ := rightBlock_bound_sub (fRF m) (Term.const (1)) _ h
      exact aux_ne_Rv aF i hi)
    (fun h => aux_notin_range_Rv aF (rightBlock_readVars_sub (fRF m)
      (Term.const (1)) (hfRF m hm) (by simp [Term.fv]) h))
    (fun h => aux_notin_range_Rv aF (rightBlock_boundSet_sub (fRF m)
      (Term.const (1)) h))
    (fun h => aux_notin_range_Lv aF (hdomLF h))
    (fun h => aux_notin_range_Rv aF (hdomRF h))
    (aux_notin_gs9R 1 r m) hboxes
    (esFG r m hr hm dt hdt σ' (by simpa [cst] using ceil_of_FM9R r m hσ'.1) hσ'.2.2)
  rw [hupd] at hbase
  refine faModalB_strengthen_plant ?_ hbase
  intro ν μ hplant hsem
  have hdomLν : Formula.sat domLF ν := sem_ode_ends_in_domain hplant.1
  have hdomRμ : Formula.sat domRF μ := sem_ode_ends_in_domain hsem
  have hdomLμ : Formula.sat domLF μ := by
    rwa [(Formula.coincidence domLF (fun v hv' => sem_ode_mask hsem (by
      obtain ⟨i, rfl⟩ := hdomLF hv'
      intro hb
      obtain ⟨j, hj⟩ := rightBlock_bound_sub (fRF m) (Term.const (1)) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))) :
        Formula.sat domLF μ ↔ Formula.sat domLF ν)]
  exact ⟨hdomLμ, hdomRμ⟩

theorem couple1R (r m : ℕ) (hr : r < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdR r m) :
    ∀ σ, Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF) σ →
      faModalB (Equiv.refl (Var 12))
        (Program.ode (DLCalTiming.clk tgF (leftBlock (fLF r))) domLF)
        (Program.ode (rightBlock (fRF m) (Term.const 1)) domRF)
        (Formula.and (FM (gR r) (gs9R r m)) envF) tgF dt
        (Function.update σ tgF 0) := by
  intro σ hσ
  have htgφ : tgF ∉ (Formula.and (FM (gR r) (gs9R r m)) envF).fv := by
    intro h
    rcases h with h | h
    · exact htgF9R r m h
    · exact htgenvF h
  have hupdφ : Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF)
      (Function.update σ tgF 0) := by
    rwa [(Formula.coincidence (Formula.and (FM (gR r) (gs9R r m)) envF) (fun v hv' =>
      Function.update_of_ne (fun hc => htgφ (by rw [← hc]; exact hv')) _ _) :
        Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF) _ ↔ _)]
  refine faModalB_monoQ ?_ (coupleR r m hr hm dt hdt hv
    (Function.update σ tgF 0) hupdφ (Function.update_self _ _ _))
  intro ν μ hsem
  exact sem_rightBlock_reparam (1) 1 (by norm_num) one_pos hsem

/-- The window response at row `r`: hop prefix to right mode `m`, two coupled pieces
there, the region at `m` owed. -/
theorem respondR (r m : ℕ) (hr : r < 3) (hm : m < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : VerdR r m) (path : List ℕ) (hpath : ∀ p ∈ path, p < 3)
    {σ : State (Var 12)}
    (hσE : Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF) σ) :
    Formula.sat (faModal (Equiv.refl (Var 12))
      (windowSeg (leftBlock (fLF r)) domLF tgF dt 2)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRF p) (Term.const 1)) domRF))
        ++ [Program.ode (rightBlock (fRF m) (Term.const 1)) domRF,
            Program.ode (rightBlock (fRF m) (Term.const 1)) domRF]))
      (Formula.and (Formula.and (FRow r) envF) (regionF m))) σ := by
  have hfa := Hmulti_windowRF_prefixed (fLF r) domLF (FM (gR r) (gs9R r m)) envF
    aF dt 2 (htgF9R r m) htgenvF
    (path.map (fun p => (⟨fRF p, Term.const 1, domRF⟩ : RepoHop 12)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfRF p (hpath p hp), by simp [Term.fv], hdomRF⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' htg'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fRF p)
        (lam := Term.const 1) (domR := domRF) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfLF r hr) hdomLF
    (List.replicate 2 (Program.ode (rightBlock (fRF m) (Term.const 1)) domRF))
    (by simp) (by norm_num)
    (by
      intro Q hQ
      rw [List.eq_of_mem_replicate hQ, Program.rename_refl]
      exact hdisH_progR (⟨fRF m, Term.const 1, domRF⟩ : RepoHop 12)
        (hfRF m hm) (by simp [Term.fv]) hdomRF (hfLF r hr) hdomLF)
    (by
      intro Q hQ σ' hσ'
      rw [List.eq_of_mem_replicate hQ]
      exact couple1R r m hr hm dt hdt hv σ' hσ')
    hσE
  rw [show (path.map (fun p => (⟨fRF p, Term.const 1, domRF⟩ : RepoHop 12))).map
      (fun h => h.progR)
      = path.map (fun p => Program.ode (rightBlock (fRF p) (Term.const 1)) domRF)
    from by rw [List.map_map]; rfl] at hfa
  have hfa2 : Formula.sat (faModal (Equiv.refl (Var 12))
      (windowSeg (leftBlock (fLF r)) domLF tgF dt 2)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fRF p) (Term.const 1)) domRF))
        ++ [Program.ode (rightBlock (fRF m) (Term.const 1)) domRF,
            Program.ode (rightBlock (fRF m) (Term.const 1)) domRF]))
      (Formula.and (FM (gR r) (gs9R r m)) envF)) σ := by
    simpa [List.replicate] using hfa
  refine sat_faModal_monoPost ?_ hfa2
  intro ν hν
  refine ⟨⟨FM_drop9R r m hν.1, hν.2⟩, ?_⟩
  rw [sat_regionF_iff]
  simpa [cst] using ceil_of_FM9R r m hν.1

/-- Row `r`'s step provider: climb to `max(r, q)`, the region at the start received and the
region at the landing mode owed. -/
theorem HmultiR (r : ℕ) (hr : r < 3) (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : ∀ m, m < 3 → r ≤ m → VerdR r m) :
    ∀ (q : ℕ), q < GrF.modes.length → ∀ σ, σ mvF = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FRow r) envF) (regionF q)) σ →
      ∃ segs : List (ℕ × RMode (Var 12) × REdge (Var 12)),
        (∀ s ∈ segs, GrF.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrF.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 12))
          (windowSeg (leftBlock (fLF r)) domLF tgF dt 2)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FRow r) envF)
            (regionF (qfOf segs q)))) σ := by
  intro q hq σ hmv hσreg
  obtain ⟨hσ, hreg⟩ := hσreg
  have hq3 : q < 3 := by simpa [GrF] using hq
  have hstep : ∀ (a b : ℕ × RMode (Var 12) × REdge (Var 12)) rest,
      a.2.2.tgt = b.1 → List.IsChain (fun x y => x.2.2.tgt = y.1) (b :: rest) →
      List.IsChain (fun x y => x.2.2.tgt = y.1) (a :: b :: rest) := by
    intro a b rest hab hrest
    refine hrest.cons ?_
    intro y hy
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hab
  have hhead1 : ∀ (a : ℕ × RMode (Var 12) × REdge (Var 12)) rest s,
      (a :: rest : List _).head? = some s → s = a := by
    intro a rest s hs
    simpa [List.head?_cons] using hs.symm
  have halign : ∀ st tgt : ℕ, st < 3 → tgt < 3 → edgeF st tgt ∈ GrF.edges →
      GrF.modeAt st = some (modeF st) ∧ edgeF st tgt ∈ GrF.edgesFrom st :=
    fun st tgt hs ht he => ⟨GrF_modeAt st hs, edgeF_mem st tgt he⟩
  have hregv : σ (Rv 0) ≤ (if q = 0 then 3/10 else if q = 1 then 1/2 else 13/20) :=
    (sat_regionF_iff q σ).mp hreg
  have henr : ∀ m : ℕ, m < 3 → q ≤ m →
      Formula.sat (Formula.and (FM (gR r) (gs9R r m)) envF) σ :=
    fun m hm3 hqm => ⟨FM_add9R r m hσ.1 (by
      simpa [cst] using le_trans hregv (cstF_mono hq3 hm3 hqm)), hσ.2⟩
  interval_cases r <;> interval_cases q
  · refine ⟨[(0, modeF 0, edgeF 0 0), (0, modeF 0, edgeF 0 0)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 0 0 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 0 0 hr (by norm_num) dt hdt (hv 0 (by norm_num) (by norm_num)) [] (by simp)
        (henr 0 (by norm_num) (by norm_num))
      have hq : qfOf [(0, modeF 0, edgeF 0 0), (0, modeF 0, edgeF 0 0)] 0 = 0 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 0 1 hr (by norm_num) dt hdt (hv 1 (by norm_num) (by norm_num)) [] (by simp)
        (henr 1 (by norm_num) (by norm_num))
      have hq : qfOf [(1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)] 1 = 1 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 0 2 hr (by norm_num) dt hdt (hv 2 (by norm_num) (by norm_num)) [] (by simp)
        (henr 2 (by norm_num) (by norm_num))
      have hq : qfOf [(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)] 2 = 2 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(0, modeF 0, edgeF 0 1), (1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact halign 0 1 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (hstep _ _ _ rfl (by simp)))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 1 1 hr (by norm_num) dt hdt (hv 1 (by norm_num) (by norm_num)) [0] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)
        (henr 1 (by norm_num) (by norm_num))
      have hq : qfOf [(0, modeF 0, edgeF 0 1), (1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)] 0 = 1 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 1 1 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 1 1 hr (by norm_num) dt hdt (hv 1 (by norm_num) (by norm_num)) [] (by simp)
        (henr 1 (by norm_num) (by norm_num))
      have hq : qfOf [(1, modeF 1, edgeF 1 1), (1, modeF 1, edgeF 1 1)] 1 = 1 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 1 2 hr (by norm_num) dt hdt (hv 2 (by norm_num) (by norm_num)) [] (by simp)
        (henr 2 (by norm_num) (by norm_num))
      have hq : qfOf [(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)] 2 = 2 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(0, modeF 0, edgeF 0 1), (1, modeF 1, edgeF 1 2), (2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact halign 0 1 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 1 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (hstep _ _ _ rfl (hstep _ _ _ rfl (by simp))))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 2 2 hr (by norm_num) dt hdt (hv 2 (by norm_num) (by norm_num)) [0, 1] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> norm_num)
        (henr 2 (by norm_num) (by norm_num))
      have hq : qfOf [(0, modeF 0, edgeF 0 1), (1, modeF 1, edgeF 1 2), (2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)] 0 = 2 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(1, modeF 1, edgeF 1 2), (2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact halign 1 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (hstep _ _ _ rfl (by simp)))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 2 2 hr (by norm_num) dt hdt (hv 2 (by norm_num) (by norm_num)) [1] (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl <;> norm_num)
        (henr 2 (by norm_num) (by norm_num))
      have hq : qfOf [(1, modeF 1, edgeF 1 2), (2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)] 1 = 2 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this
  · refine ⟨[(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
      · exact halign 2 2 (by norm_num) (by norm_num) (by simp [GrF])
    · exact (hstep _ _ _ rfl (by simp))
    · exact fun s hs => by rw [hhead1 _ _ _ hs]
    · have := respondR 2 2 hr (by norm_num) dt hdt (hv 2 (by norm_num) (by norm_num)) [] (by simp)
        (henr 2 (by norm_num) (by norm_num))
      have hq : qfOf [(2, modeF 2, edgeF 2 2), (2, modeF 2, edgeF 2 2)] 2 = 2 := rfl
      rw [hq]
      simpa [modeF, List.replicate] using this

/-! ## The left automaton, from the file -/

def nextF : List (List ℕ) :=
  (List.range 3).map (fun l =>
    (mLF l).next.filterMap (Handoff.leftModeIndex story1_attdist_rung_b_12dof_IR))

/-- `STEEP → [MODER, STEEP]`, `MODER → [FLAT, MODER]`, `FLAT → [FLAT]`. -/
theorem nextF_eq : nextF = [[1, 0], [2, 1], [2]] := by decide

theorem nextF_transitions :
    ((List.range 3).flatMap (fun m' => (nextF.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions story1_attdist_rung_b_12dof_IR := by decide

noncomputable def guardsF : List (Formula (Var 12)) :=
  (List.range 3).map (fun l => hostGuard vsF 12 Side.L (mLF l))

noncomputable def AF (dt : ℝ) : LeftAut 12 :=
  { windows := (List.range 3).map (fun l => windowSeg (leftBlock (fLF l)) domLF tgF dt 2),
    guards := guardsF,
    next := nextF }

theorem AF_numModes (dt : ℝ) : (AF dt).numModes = 3 := rfl

theorem AF_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AF dt).window t = windowSeg (leftBlock (fLF t)) domLF tgF dt 2 := by
  interval_cases t <;> rfl

theorem AF_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AF dt).guard t = hostGuard vsF 12 Side.L (mLF t) := by
  interval_cases t <;> rfl

theorem AF_succ (dt : ℝ) (m' : ℕ) : (AF dt).succ m' = nextF.getD m' [] := rfl

theorem hnextF (dt : ℝ) : ∀ m' < (AF dt).numModes, ∀ t ∈ (AF dt).succ m', t < (AF dt).numModes := by
  intro m' hm' t ht
  rw [AF_numModes] at hm' ⊢
  rw [AF_succ, nextF_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardF (t : ℕ) (ht : t < 3) : (hostGuard vsF 12 Side.L (mLF t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsF (mLF t) ?_
  interval_cases t <;>
    simp [mLF, story1_attdist_rung_b_12dof_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdF (dt : ℝ) : ∀ t < (AF dt).numModes, ((AF dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AF_numModes] at ht
  rw [AF_guard dt t ht]
  exact hguardF t ht

theorem hwinF (dt : ℝ) : ∀ t < (AF dt).numModes,
    Program.vars ((AF dt).window t) ⊆ {((Side.Aux, 1) : Var 12)} ∪ range Lv := by
  intro t ht
  rw [AF_numModes] at ht
  rw [AF_window dt t ht]
  exact vars_windowSegL_sub (fLF t) domLF 1 dt 2 (hfLF t ht) hdomLF

/-! ## Freshness of `u_L` -/

theorem hulenvF : ulF ∉ envF.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRF h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem hulBkF : ulF ∉ (mvRegion mvF regionF GrF.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mvF regionF GrF.modes.length (fun q _ => regionF_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulGF (dt : ℝ) : ∀ t, ulF ∉ ((AF dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrdF dt t ht h)
  · have : (AF dt).guard t = Formula.tt := by
      unfold LeftAut.guard AF guardsF
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlF (dt : ℝ) : ∀ t, FramesMv ((AF dt).window t) ulF := by
  intro t
  by_cases ht : t < 3
  · rw [AF_window dt t ht]
    refine framesMv_window (leftBlock (fLF t)) domLF tgF dt 2 ulF (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (AF dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AF
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRF : ulF ∉ (rightAutomatonBody GrF mvF).bv :=
  notMem_bv_rightAutomatonBody GrF mvF ulF (by decide) (aux_notin_range_Rv 2) httF hRvF

/-! ## The handoff: nested rows, in-kernel -/

theorem handoffF (dt : ℝ) : ∀ m' < (AF dt).numModes, ∀ t ∈ (AF dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat ((AF dt).guard t) ω → Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _
  rw [AF_numModes] at hm'
  rw [AF_succ, nextF_eq] at ht
  have hm3 : m' < 3 := hm'
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl
  · -- STEEP → MODER: drop the `v` conjunct
    refine FM_mono ?_ hF
    intro g hg
    simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    rcases hg with rfl | rfl
    · exact Or.inr (Or.inl gRowAt_one_zero)
    · exact Or.inr (Or.inr gRowAt_one_one)
  · exact hF
  · -- MODER → FLAT: identical rows
    rw [FRow_two_eq_one]; exact hF
  · exact hF
  · exact hF

/-! ## The per-mode steps -/

theorem hstepMF (dt : ℝ) (hdt : 0 ≤ dt)
    (hv : ∀ r m, r < 3 → m < 3 → r ≤ m → VerdR r m) :
    ∀ t < (AF dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envF)
      (mvRegion mvF regionF GrF.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 12)) ((AF dt).window t)
      (Program.star (rightAutomatonBody GrF mvF))
      (Formula.and (Formula.and (FRow t) envF)
        (mvRegion mvF regionF GrF.modes.length))) σ := by
  intro t ht
  rw [AF_numModes] at ht
  rw [AF_window dt t ht]
  have hframe : FramesMv (windowSeg (leftBlock (fLF t)) domLF tgF dt 2) mvF := by
    refine framesMv_window (leftBlock (fLF t)) domLF tgF dt 2 mvF (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLF t) _ h
    exact aux_ne_Lv 0 i hi
  exact hstepMode_multiR GrF mvF (FRow t) envF regionF _ (aux_notin_FRow 0 t) hmvenvF hmvregF
    hfreshF httF hltF hframe
    (HmultiR t ht dt hdt (fun m hm hrm => hv t m ht hm hrm))

/-! ## The composed theorem -/

/-- **`story1_attdist_rung_b_12dof`, Theorem 3 at the DECLARED mode-dependent invariant.**
`u_L`-keyed: the STEEP window at `v[l] ≤ v[r] ∧ D_ψ ∧ D_θ`, the MODER and FLAT windows at
`D_ψ ∧ D_θ`, over the left automaton `STEEP → MODER → FLAT` (with self-loops), with each
right mode's checked-cut ceiling riding the loop invariant as its region (`mvRegionR`), as
in the base instance. Residuals: the six climb packs `VerdR r m` (`r ≤ m`). -/
theorem story1_attdist_rung_b_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt)
    (hv00 : VerdR 0 0) (hv01 : VerdR 0 1) (hv02 : VerdR 0 2)
    (hv11 : VerdR 1 1) (hv12 : VerdR 1 2) (hv22 : VerdR 2 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AF dt) ulF)
      (rightAutomatonBody GrF mvF)
      (psiK ulF ϕRow (AF dt).numModes domLF domRF
        (mvRegionR mvF regionF GrF.modes.length))) := by
  have hv : ∀ r m, r < 3 → m < 3 → r ≤ m → VerdR r m := by
    intro r m hr hm hrm
    interval_cases r <;> interval_cases m <;> first | assumption | omega
  refine theorem3_modeKeyed (AF dt) ulF GrF mvF FRow ϕRow domLF domRF
    (mvRegion mvF regionF GrF.modes.length) (mvRegionR mvF regionF GrF.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AF dt) GrF 0 1 2 (by decide) (by decide) (hwinF dt) (hgrdF dt)
      (hnextF dt) httF hRvF
  · exact hstep_modeKeyed (AF dt) ulF (rightAutomatonBody GrF mvF) FRow envF
      (mvRegion mvF regionF GrF.modes.length) (aux_notin_FRow 2) hulenvF hulBkF (hulGF dt)
      (hframesUlF dt) hulRF (hnextF dt) (hstepMF dt hdt hv) (handoffF dt)
  · exact hddF_modeKeyed (AF dt) GrF 0 1 2 (by decide) (by decide) ϕRow domLF domRF
      (mvRegionR mvF regionF GrF.modes.length) (hwinF dt) (hgrdF dt) (hnextF dt) httF hRvF
      (fun m _ => canonInvM_varsL (gR m) (gsR m) (fun g' hg' => by
        obtain ⟨i, rfl⟩ := mem_gsR hg'
        exact hgRowAt m i))
      (fun m _ => canonInvM_varsR (gR m) (gsR m)) hdomLF hdomRF rfl
      (fun v hv => mvRegion_fv_sub mvF regionF GrF.modes.length (fun q _ => regionF_fv q) hv)

end Story1AttdistRungBHandoff
end RelCertifier

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The generic bridge, part 4: the anchor of a window and right mode

`AG l q` (the row, the kept atoms of both modes, the barrier terms of `q`'s pruned exits, the
envelope) is what the cover's induction carries. Here, from the structural bundle `structOK`
and the verdicts (stays, non-connection pairs, flow packs, reposition packs):

* `AG_fv`, `AG_dom`, `AG_post`: hygiene, the envelope, the post of a segment;
* `AG_start`: an admissible start satisfies the anchor (left atoms from the guard, right atoms
  from the region, barriers from the source checks);
* `AG_hand`: the anchor transfers along a legal switch (the entered mode's atoms from its
  guard, its barriers from its source checks);
* `AG_box`: a joint segment at the pairing's stretch keeps the anchor (the pack, the stays, the
  barriers' strict DI);
* `AG_boxD`: a frozen-left segment keeps it (the reposition pack);
* `AG_prune`, `AG_pruneD`: a pruned exit's guard never holds at the end of a segment.
-/
import RelCertifier.Proofs.Encoding.Emitted.Barrier
import RelCertifier.Proofs.Encoding.ReplayDyn

set_option autoImplicit false

namespace RelCertifier
namespace Emitted

open DL Parse Run Set Oracle Bridge

variable {n : ℕ}

/-! ## Reading the structural bundle -/

section Read

variable {p : PProblem} {cov : CoverEmitE} {cX : EvolStrengtheningX}

theorem find?_name_of_nodup {ms : List PMode} (hnd : (ms.map (·.name)).Nodup) {m : PMode}
    (hm : m ∈ ms) : ms.find? (·.name == m.name) = some m := by
  induction ms with
  | nil => simp at hm
  | cons a as ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact List.find?_cons_of_pos (by simp)
      · have hne : a.name ≠ m.name := by
          intro h
          rw [List.map_cons, List.nodup_cons] at hnd
          exact hnd.1 (h ▸ List.mem_map.mpr ⟨m, hm', rfl⟩)
        rw [List.find?_cons_of_neg (by simpa using hne)]
        exact ih (List.nodup_cons.mp (by simpa using hnd)).2 hm'

theorem cutsOK_wfX (h : cutsOK p n cX = true) : evolStrengtheningWFX p cX = true := by
  simp only [cutsOK, Bool.and_eq_true] at h; exact h.1.1.1.1

theorem atomsWF_L (h : cutsOK p n cX = true) {l : ℕ} (hl : l < nL p) :
    atomsWF (vars p) n Side.L "R_" (cutAtomsOfX cX.L (mLof p l).name) = true := by
  simp only [cutsOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.2 _ (mLof_mem hl)

theorem atomsWF_R (h : cutsOK p n cX = true) {q : ℕ} (hq : q < nR p) :
    atomsWF (vars p) n Side.R "L_" (cutAtomsOfX cX.R (mRof p q).name) = true := by
  simp only [cutsOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.2 _ (mRof_mem hq)

/-- Out of range, a right index names no certificate entry (or a declared mode's): its atom
list passes the checks as well. -/
theorem atomsWF_R_any (h : cutsOK p n cX = true) (q : ℕ) :
    atomsWF (vars p) n Side.R "L_" (cutAtomsOfX cX.R (mRof p q).name) = true := by
  by_cases hq : q < nR p
  · exact atomsWF_R h hq
  · rw [mRof_dm hq]
    simp only [cutsOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
    rcases hfind : cX.R.find? (·.1 == dm.name) with _ | e
    · simp [cutAtomsOfX, hfind, atomsWF]
    · obtain ⟨m, hm, hname⟩ := h.2 e (List.mem_of_find?_eq_some hfind)
      have hed : e.1 = dm.name := by simpa using List.find?_some hfind
      have := h.1.1.2 m hm
      rwa [hname, hed] at this

theorem atomsWF_mem {vars : List String} {side : Side} {bad : String} {atoms : List CutAtomX}
    (h : atomsWF vars n side bad atoms = true) {x : CutAtomX} (hx : x ∈ atoms) :
    atomOK vars n side bad x = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact (atomsWF_at h (List.getElem?_eq_getElem hi)).1

theorem lowers_L (h : lowersOK p n = true) {l : ℕ} (hl : l < nL p) :
    (lowerF (vars p) n Side.L (mLof p l).guard).isSome = true ∧
    (lowerF (vars p) n Side.L (mLof p l).evolve).isSome = true ∧
    (dynOf (vars p) n Side.L (mLof p l)).isSome = true := by
  simp only [lowersOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 _ (mLof_mem hl)
  exact ⟨h1, h2, h3⟩

theorem lowers_R (h : lowersOK p n = true) {q : ℕ} (hq : q < nR p) :
    (lowerF (vars p) n Side.R (mRof p q).guard).isSome = true ∧
    (lowerF (vars p) n Side.R (mRof p q).evolve).isSome = true ∧
    (dynOf (vars p) n Side.R (mRof p q)).isSome = true := by
  simp only [lowersOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.2 _ (mRof_mem hq)
  exact ⟨h1, h2, h3⟩

theorem rowsOK_at (h : rowsOK p n = true) {l : ℕ} (hl : l < nL p) : 0 < compsLen p n l := by
  simp only [rowsOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h l hl

theorem timeOK_at (h : timeOK p cov = true) {l : ℕ} (hl : l < nL p) :
    0 < epsR p ∧ 0 < epsL p ∧ 0 < ((coverOf p cov l).lamQ : ℝ) ∧
    epsL p * ((coverOf p cov l).lamQ : ℝ) ≤ (B p cov l : ℝ) * epsR p ∧
    ∀ q < nR p, 0 < lam p cov l q ∧ lam p cov l q ≤ ((coverOf p cov l).lamQ : ℝ) := by
  simp only [timeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨heR, heL⟩, hall⟩ := h
  obtain ⟨⟨hlamQ, hbud⟩, hq⟩ := hall l hl
  refine ⟨by unfold epsR; exact_mod_cast heR, by unfold epsL; exact_mod_cast heL,
    by exact_mod_cast hlamQ, ?_, fun q hq' => ?_⟩
  · unfold epsL epsR B
    have := hbud
    rw [ge_iff_le] at this
    exact_mod_cast this
  · obtain ⟨⟨hN, hD⟩, hle⟩ := hq q hq'
    refine ⟨?_, by unfold lam; exact_mod_cast hle⟩
    unfold lam lamQ
    have : (0 : ℚ) < ((strataOf p cov l q).lamN : ℚ) / ((strataOf p cov l q).lamD : ℚ) :=
      div_pos (by exact_mod_cast hN) (by exact_mod_cast hD)
    exact_mod_cast this

theorem permOK_joint (h : permOK p n cov = true) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (hj : (flagsOf p cov l q).jointOK = true) :
    (strataOf p cov l q).order.Perm (List.range (compsLen p n l)) := by
  simp only [permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
  rcases (h l hl q hq).1.1 with h' | h'
  · rw [hj] at h'; exact absurd h' (by decide)
  · exact h'

theorem permOK_dyn (h : permOK p n cov = true) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (pre : Bool) (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true) :
    (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder).Perm
      (List.range (compsLen p n l)) := by
  simp only [permOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hpre⟩, hpost⟩ := h l hl q hq
  cases pre with
  | true =>
      simp only [↓reduceIte] at hd ⊢
      rcases hpre with h' | h'
      · rw [hd] at h'; exact absurd h' (by decide)
      · exact h'
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hd ⊢
      rcases hpost with h' | h'
      · rw [hd] at h'; exact absurd h' (by decide)
      · exact h'

theorem rowsByName_at (h : rowsByName p = true) {l : ℕ} (hl : l < nL p) :
    Handoff.invRowOf p (mLof p l) = some (rowOf p l) := by
  simp only [rowsByName, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h l hl

end Read

/-! ## The verdicts of a benchmark -/

section Verdicts

variable (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)

/-- The stays of every mode's kept atoms. -/
def StayAll : Prop :=
  (∀ l < nL p, StayVerd (vars p) n Side.L (mLof p l) (cutAtomsOfX cX.L (mLof p l).name)) ∧
  (∀ q < nR p, StayVerd (vars p) n Side.R (mRof p q) (cutAtomsOfX cX.R (mRof p q).name))

/-- The non-connection pair of every pruned edge. -/
def NonConnAll : Prop :=
  ∀ q < nR p, ∀ t ∈ prunedTgts p cov q,
    NonConnVerd (vars p) n (cutAtomsOfX cX.R (mRof p q).name) (mRof p q) (mRof p t)

/-- The flow pack of a certified pairing, at its strata order and stretch. -/
def JointVerd (l q : ℕ) : Prop :=
  modalVerdX p cX n (rowIdx p l) (strataOf p cov l q).order (lam p cov l q) l q

/-- The reposition pack of a pairing. -/
def DynVerd (l q : ℕ) (pre : Bool) : Prop :=
  modalVerdDynX p cX n (rowIdx p l)
    (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder) pre l q

/-- The ordered components of a window's row under a strata order. -/
noncomputable def compsAt (l : ℕ) (order : List ℕ) : List (Term (Var n)) :=
  order.map (fun i => (comps p n l).getD i (Term.const 0))

end Verdicts

section Anchor

variable {p : PProblem} {cX : EvolStrengtheningX} {cov : CoverEmitE}
  (hs : structOK p n cov cX = true)

include hs

theorem hu : uniformEvolve p = true := (structOK_iff.mp hs).1
theorem hnames : namesOK p = true := (structOK_iff.mp hs).2.1
theorem hres : namesResolve p = true := (structOK_iff.mp hs).2.2.1
theorem hrows : rowsOK p n = true := (structOK_iff.mp hs).2.2.2.1
theorem htime : timeOK p cov = true := (structOK_iff.mp hs).2.2.2.2.1
theorem hlow : lowersOK p n = true := (structOK_iff.mp hs).2.2.2.2.2.1
theorem hperm : permOK p n cov = true := (structOK_iff.mp hs).2.2.2.2.2.2.2.1
theorem hcuts : cutsOK p n cX = true := (structOK_iff.mp hs).2.2.2.2.2.2.2.2.1

theorem hiffL {l : ℕ} (hl : l < nL p) : AtomsIff (cL p n cX l) :=
  atomsIff_of_WF (atomsWF_L (hcuts hs) hl)
theorem hiffR {q : ℕ} (hq : q < nR p) : AtomsIff (cR p n cX q) :=
  atomsIff_of_WF (atomsWF_R (hcuts hs) hq)

theorem lam_pos {l q : ℕ} (hl : l < nL p) (hq : q < nR p) : 0 < lam p cov l q :=
  ((timeOK_at (htime hs) hl).2.2.2.2 q hq).1

/-- The left atoms of window `l` stay along any joint flow at any stretch, inside the
envelope. -/
theorem stayL_env {l : ℕ} (hl : l < nL p) (hst : StayAll p n cX) (fR' : Fin n → Term (Var n))
    (lam' : Term (Var n)) :
    AtomsStayC (cL p n cX l) (jointSys (fL p n l) fR' lam') (env p n) :=
  atomsStayC_L (vars p) (mLof p l) _ (atomsWF_L (hcuts hs) hl) (hst.1 l hl) fR' lam' (env p n)
    (fun z hz => by rw [hostEvolve_L (hu hs) hl]; exact hz.1)

/-- The right atoms of mode `q` stay along any joint flow of its field at a positive stretch,
inside a domain within the envelope. -/
theorem stayR_dom {q : ℕ} (hq : q < nR p) (hst : StayAll p n cX) (fL' : Fin n → Term (Var n))
    (c : ℝ) (hc : 0 < c) (dom : Formula (Var n)) (hdom : ∀ z, Formula.sat dom z → Formula.sat (domR p n) z) :
    AtomsStayC (cR p n cX q) (jointSys fL' (fR p n q) (Term.const c)) dom :=
  atomsStayC_R (vars p) (mRof p q) _ (atomsWF_R (hcuts hs) hq) (hst.2 q hq) fL' c hc dom
    (fun z hz => by rw [hostEvolve_R (hu hs) hq]; exact hdom z hz)

theorem cutsR_of_guard {q : ℕ} (hq : q < nR p) :
    ∀ ν, Formula.sat (guardR p n q) ν → CutSat (cR p n cX q) ν := by
  have hwf := atomsWF_R (hcuts hs) hq
  refine cutSatR_of_guard (cutsOK_wfX (hcuts hs)) (mRof p q) ?_ ?_ ?_ (lowers_R (hlow hs) hq).1
  · refine find?_name_of_nodup ?_ (mRof_mem hq)
    have := hres hs
    simp only [namesResolve, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  · intro x hx; exact atomOK_entry (atomsWF_mem hwf hx)
  · intro x hx; exact atomOK_lowers (atomsWF_mem hwf hx)

theorem cutsL_of_guard {l : ℕ} (hl : l < nL p) :
    ∀ ν, Formula.sat (guardL p n l) ν → CutSat (cL p n cX l) ν := by
  have hwf := atomsWF_L (hcuts hs) hl
  refine cutSatL_of_guard (cutsOK_wfX (hcuts hs)) (mLof p l) ?_ ?_ ?_ (lowers_L (hlow hs) hl).1
  · refine find?_name_of_nodup ?_ (mLof_mem hl)
    have := hres hs
    simp only [namesResolve, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  · intro x hx; exact atomOK_entry (atomsWF_mem hwf hx)
  · intro x hx; exact atomOK_lowers (atomsWF_mem hwf hx)

/-! ### The pruned exits of a mode -/

omit hs in
theorem barrierOf_eq (t : ℕ) : barrierOf p n t = hostBarrier (vars p) n (mRof p t) := rfl

theorem prunedTgts_lt {q : ℕ} (hq : q < nR p) {t : ℕ} (ht : t ∈ prunedTgts p cov q) : t < nR p := by
  unfold prunedTgts at ht
  obtain ⟨nm, hnm, rfl⟩ := List.mem_map.mp ht
  exact tgtIdx_lt (hres hs) hq (List.mem_of_mem_filter hnm)

omit hs in
theorem mem_prunedTgts {q : ℕ} {e : REdge (Var n)} {pr : String → String → Bool}
    (he : e ∈ (grOf p n pr).edgesFrom q) (hpr : pr = prunedOf cov) (hp : e.pruned = true) :
    e.tgt ∈ prunedTgts p cov q := by
  obtain ⟨nm, hnm, htgt, hpe⟩ := grOf_pruned he
  rw [htgt]
  refine List.mem_map.mpr ⟨nm, List.mem_filter.mpr ⟨hnm, ?_⟩, rfl⟩
  rw [← hpr, ← hpe, hp]

/-- The barriers hold on entering `q` (its guard, the envelope, its atoms). -/
theorem barriers_entry (hnc : NonConnAll p n cX cov) {q : ℕ} (hq : q < nR p) (y : State (Var n))
    (hg : Formula.sat (guardR p n q) y) (hd : Formula.sat (domR p n) y) :
    ∀ b ∈ barriers p n cov q, Term.eval b y ≤ 0 := by
  intro b hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  rw [barrierOf_eq]
  refine nonconn_entry (hnc q hq t ht) y hg ?_ (cutsR_of_guard hs hq y hg)
  rw [hostEvolve_R (hu hs) hq]; exact hd

/-- The barriers are kept along any flow of `q`'s field inside the envelope that starts in
`q`'s atoms. -/
theorem barriers_keep (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {q : ℕ} (hq : q < nR p)
    (fL' : Fin n → Term (Var n)) (c : ℝ) (hc : 0 < c) :
    ∀ σ ω, CutSat (cR p n cX q) σ → (∀ b ∈ barriers p n cov q, Term.eval b σ ≤ 0) →
      Program.sem (Program.ode (jointSys fL' (fR p n q) (Term.const c)) (env p n)) σ ω →
      ∀ b ∈ barriers p n cov q, Term.eval b ω ≤ 0 := by
  intro σ ω hcσ hbσ hω b hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  have hB := nonconn_keep (hnc q hq t ht) (atomsWF_R (hcuts hs) hq)
    (names_R (hnames hs) t).1 fL' c hc (env p n)
    (fun z hz => by rw [hostEvolve_R (hu hs) hq]; exact hz.2)
    (stayR_dom hs hq hst fL' c hc (env p n) (fun z hz => hz.2)) σ hcσ
    (by rw [← barrierOf_eq]; exact hbσ _ hb)
  rw [barrierOf_eq]
  exact hB ω hω

/-- A barrier `≤ 0` excludes the pruned target's guard. -/
theorem not_guard_of_barrier (hnc : NonConnAll p n cX cov) {q : ℕ} (hq : q < nR p) {t : ℕ}
    (ht : t ∈ prunedTgts p cov q) (ω : State (Var n)) (hb : Term.eval (barrierOf p n t) ω ≤ 0) :
    ¬ Formula.sat (guardR p n t) ω := by
  intro hg
  have htlt := prunedTgts_lt hs hq ht
  obtain ⟨gf, hgf⟩ := Option.isSome_iff_exists.mp (lowers_R (hlow hs) htlt).1
  have := guard_pos_of_barrier (hnc q hq t ht) hgf ω hg
  rw [barrierOf_eq] at hb
  linarith

/-! ### The anchor -/

theorem AG_fv {l q : ℕ} (hl : l < nL p) (hq : q < nR p) :
    (AG p n cX cov l q).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  rcases hv with hv | hv | hv
  · by_contra hc
    refine notMem_FM_fv (fun g' hg' hx => hc ?_) hv
    have hcg := cons_g_gs p n l (rowsOK_at (hrows hs) hl)
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact hostComps_fv _ _ _ (hcg ▸ List.mem_cons_self) hx
    rcases List.mem_append.mp hg' with hg' | hg'
    · rcases List.mem_append.mp hg' with hg' | hg'
      · exact hostComps_fv _ _ _ (List.mem_of_mem_tail hg') hx
      · simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
        rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · exact Or.inl (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl) a ha hx)
        · exact Or.inr (cutPairsX_fv_R (atomsWF_R (hcuts hs) hq) a ha hx)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg'
      have hfree := (names_R (hnames hs) t).1
      unfold barrierOf at hx
      rcases hgt : NonConn.guardTerm (vars p) n (mRof p t).guard with _ | gI
      · rw [hgt] at hx; simp [Term.fv] at hx
      · rw [hgt] at hx
        simp only [Option.map_some, Option.getD_some] at hx
        exact Or.inr (side_eq_R_mem (guardTerm_fv hfree hgt v hx))
  · exact Or.inl (domL_fv (hnames hs) hv)
  · exact Or.inr (domR_fv (hnames hs) hv)

omit hs in
theorem AG_dom {l q : ℕ} (y : State (Var n)) (h : Formula.sat (AG p n cX cov l q) y) :
    Formula.sat (domR p n) y := h.2.2

theorem AG_post {l q : ℕ} (hl : l < nL p) (hq : q < nR p) (y : State (Var n))
    (h : Formula.sat (AG p n cX cov l q) y) :
    Formula.sat (Formula.and (Formula.and (FRow p n l) (env p n)) (cuts p n cX q)) y := by
  obtain ⟨hFA, -⟩ := (sat_FM_append _ _ _ y).mp h.1
  obtain ⟨hF, hat⟩ := (sat_FM_append _ _ _ y).mp hFA
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

theorem AG_start (hnc : NonConnAll p n cX cov) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (σ : State (Var n)) (hgL : Formula.sat (guardL p n l) σ)
    (hσ : Formula.sat (Formula.and (FRow p n l) (env p n)) σ)
    (hg : Formula.sat (guardR p n q) σ) (hc : Formula.sat (cuts p n cX q) σ) :
    Formula.sat (AG p n cX cov l q) σ := by
  refine ⟨(sat_FM_append _ _ _ σ).mpr ⟨(sat_FM_append _ _ _ σ).mpr ⟨hσ.1, ?_⟩, ?_⟩, hσ.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mpr
      ⟨cutsL_of_guard hs hl σ hgL, (sat_cutF _ _).mp hc⟩
  · exact barriers_entry hs hnc hq σ hg hσ.2.2

theorem AG_hand (hnc : NonConnAll p n cX cov) {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    {pr : String → String → Bool} (e : REdge (Var n)) (he : e ∈ (grOf p n pr).edgesFrom q)
    (y : State (Var n)) (hA : Formula.sat (AG p n cX cov l q) y) (hleg : SwitchLegal e y) :
    Formula.sat (AG p n cX cov l e.tgt) y := by
  have htlt : e.tgt < nR p := by
    have := grOf_lt (hres hs) (pruned := pr) q e he; rwa [grOf_len] at this
  have hg : Formula.sat (guardR p n e.tgt) y := by
    unfold SwitchLegal at hleg; rwa [grOf_guards q e he] at hleg
  obtain ⟨hFA, -⟩ := (sat_FM_append _ _ _ y).mp hA.1
  obtain ⟨hF, hat⟩ := (sat_FM_append _ _ _ y).mp hFA
  obtain ⟨hLc, -⟩ := (atomTerms_iff (hiffL hs hl) (hiffR hs hq) y).mp hat
  refine ⟨(sat_FM_append _ _ _ y).mpr ⟨(sat_FM_append _ _ _ y).mpr ⟨hF, ?_⟩, ?_⟩, hA.2⟩
  · exact (atomTerms_iff (hiffL hs hl) (hiffR hs htlt) y).mpr ⟨hLc, cutsR_of_guard hs htlt y hg⟩
  · exact barriers_entry hs hnc htlt y hg hA.2.2

/-! ### Preservation -/

theorem comps_mem_equiv {l : ℕ} (hl : l < nL p) {order : List ℕ}
    (hperm' : order.Perm (List.range (compsLen p n l))) :
    (∀ c ∈ compsAt p n l order, c ∈ g p n l :: gs p n l) ∧
    (∀ c ∈ g p n l :: gs p n l, c ∈ compsAt p n l order) := by
  rw [cons_g_gs p n l (rowsOK_at (hrows hs) hl)]
  rw [← comps_length] at hperm'
  have := mem_equiv_of_index_perm (comps p n l) order hperm'
  exact ⟨fun c hc => (this c).mp hc, fun c hc => (this c).mpr hc⟩

theorem jointVerd_core {l q : ℕ} (hl : l < nL p) (hq : q < nR p)
    (hv : JointVerd p n cX cov l q) :
    VerdXCore (compsAt p n l (strataOf p cov l q).order) (fL p n l) (fR p n q) (lam p cov l q)
      (domCutX (env p n) (cL p n cX l) (cR p n cX q)) := by
  have h : VerdXCore (compsAt p n l (strataOf p cov l q).order) (fL p n l) (fR p n q)
      (lam p cov l q)
      (domCutX (Formula.and (hostEvolve (vars p) n Side.L (mLof p l))
        (hostEvolve (vars p) n Side.R (mRof p q))) (cL p n cX l) (cR p n cX q)) := hv
  rwa [hostEvolve_L (hu hs) hl, hostEvolve_R (hu hs) hq] at h

theorem dynVerd_core {l q : ℕ} (hl : l < nL p) (hq : q < nR p) (pre : Bool)
    (hv : DynVerd p n cX cov l q pre) :
    VerdDynCore pre (compsAt p n l
        (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder))
      (fR p n q) (domCutX (env p n) (cL p n cX l) (cR p n cX q)) (guardL p n l) := by
  have h : VerdDynCore pre (compsAt p n l
        (if pre then (strataOf p cov l q).dynPreOrder else (strataOf p cov l q).dynPostOrder))
      (fR p n q) (domCutX (Formula.and (hostEvolve (vars p) n Side.L (mLof p l))
        (hostEvolve (vars p) n Side.R (mRof p q))) (cL p n cX l) (cR p n cX q))
      (guardL p n l) := hv
  rwa [hostEvolve_L (hu hs) hl, hostEvolve_R (hu hs) hq] at h

/-- A joint segment at the pairing's stretch keeps the anchor. -/
theorem AG_box (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (hj : (flagsOf p cov l q).jointOK = true) (hv : JointVerd p n cX cov l q) :
    ∀ σ ω, Formula.sat (AG p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fL p n l) (fR p n q) (Term.const (lam p cov l q)))
        (env p n)) σ ω → Formula.sat (AG p n cX cov l q) ω := by
  intro σ ω hσ hω
  obtain ⟨hFA, hbar⟩ := (sat_FM_append _ _ _ σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := comps_mem_equiv hs hl (permOK_joint (hperm hs) hl hq hj)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp hFA
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  refine ⟨(sat_FM_append _ _ _ ω).mpr ⟨?_, ?_⟩, sem_ode_ends_in_domain hω⟩
  · exact couple_box_cutX (g p n l) (gs p n l) _ (cL p n cX l) (cR p n cX q) (fL p n l) (fR p n q)
      (lam p cov l q) (domL p n) (domR p n) hsub1 hsub2 (hiffL hs hl) (hiffR hs hq)
      (stayL_env hs hl hst _ _) (stayR_dom hs hq hst _ _ (lam_pos hs hl hq) _ (fun z hz => hz.2))
      (jointVerd_core hs hl hq hv) σ ω hFA hω
  · exact barriers_keep hs hnc hst hq (fL p n l) _ (lam_pos hs hl hq) σ ω hcRσ hbar hω

/-- A frozen-left segment keeps the anchor (pre-joint: under the left guard). -/
theorem AG_boxD (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (pre : Bool)
    (hd : (if pre then (flagsOf p cov l q).dynPre else (flagsOf p cov l q).dynPost) = true)
    (hv : DynVerd p n cX cov l q pre) :
    ∀ σ ω, Formula.sat (AG p n cX cov l q) σ → (pre = true → Formula.sat (guardL p n l) σ) →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → Formula.sat (AG p n cX cov l q) ω := by
  intro σ ω hσ hgσ hω
  obtain ⟨hFA, hbar⟩ := (sat_FM_append _ _ _ σ).mp hσ.1
  obtain ⟨hsub1, hsub2⟩ := comps_mem_equiv hs hl (permOK_dyn (hperm hs) hl hq pre hd)
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp hFA
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  refine ⟨(sat_FM_append _ _ _ ω).mpr ⟨?_, ?_⟩, sem_ode_ends_in_domain hω⟩
  · refine couple_box_dyn pre (g p n l) (gs p n l) _ (cL p n cX l) (cR p n cX q) (fR p n q)
      (domL p n) (domR p n) (guardL p n l) hsub1 hsub2 (hiffL hs hl) (hiffR hs hq)
      (cutPairsX_fv_L (atomsWF_L (hcuts hs) hl)) (guardL_fv (hnames hs) l) ?_
      (dynVerd_core hs hl hq pre hv) σ ω hFA hgσ hω
    refine stayR_dom hs hq hst (fun _ => Term.const 0) 1 one_pos _ ?_
    intro z hz
    unfold dynBase at hz
    cases pre with
    | true => exact hz.1.2
    | false => exact hz.2
  · exact barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 one_pos σ ω hcRσ hbar hω

/-- A pruned exit is never enabled after a joint segment from the anchor. -/
theorem AG_prune (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (e : REdge (Var n)) (he : e ∈ (grOf p n (prunedOf cov)).edgesFrom q)
    (hp : e.pruned = true) :
    ∀ σ ω, Formula.sat (AG p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fL p n l) (fR p n q) (Term.const (lam p cov l q)))
        (env p n)) σ ω → ¬ Formula.sat e.guard ω := by
  intro σ ω hσ hω
  have ht := mem_prunedTgts (cov := cov) he rfl hp
  obtain ⟨hFA, hbar⟩ := (sat_FM_append _ _ _ σ).mp hσ.1
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp hFA
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  have hkeep := barriers_keep hs hnc hst hq (fL p n l) _ (lam_pos hs hl hq) σ ω hcRσ hbar hω
  rw [grOf_guards q e he]
  exact not_guard_of_barrier hs hnc hq ht ω (hkeep _ (List.mem_map.mpr ⟨e.tgt, ht, rfl⟩))

/-- A pruned exit is never enabled after a frozen-left segment from the anchor. -/
theorem AG_pruneD (hnc : NonConnAll p n cX cov) (hst : StayAll p n cX) {l q : ℕ} (hl : l < nL p)
    (hq : q < nR p) (e : REdge (Var n)) (he : e ∈ (grOf p n (prunedOf cov)).edgesFrom q)
    (hp : e.pruned = true) :
    ∀ σ ω, Formula.sat (AG p n cX cov l q) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR p n q) (Term.const 1))
        (Formula.and (domL p n) (domR p n))) σ ω → ¬ Formula.sat e.guard ω := by
  intro σ ω hσ hω
  have ht := mem_prunedTgts (cov := cov) he rfl hp
  obtain ⟨hFA, hbar⟩ := (sat_FM_append _ _ _ σ).mp hσ.1
  have hcRσ : CutSat (cR p n cX q) σ := by
    obtain ⟨-, hat⟩ := (sat_FM_append _ _ _ σ).mp hFA
    exact ((atomTerms_iff (hiffL hs hl) (hiffR hs hq) σ).mp hat).2
  have hkeep := barriers_keep hs hnc hst hq (fun _ => Term.const 0) 1 one_pos σ ω hcRσ hbar hω
  rw [grOf_guards q e he]
  exact not_guard_of_barrier hs hnc hq ht ω (hkeep _ (List.mem_map.mpr ⟨e.tgt, ht, rfl⟩))

end Anchor

/-- The anchor with the region Assumption 1 is relative to (`⊤` for the suite's benchmarks,
the momentum band for the detumble family). -/
noncomputable def AGr (p : PProblem) (n : ℕ) (cX : EvolStrengtheningX) (cov : CoverEmitE)
    (reg : Formula (Var n)) (l q : ℕ) : Formula (Var n) :=
  Formula.and (AG p n cX cov l q) reg

end Emitted
end RelCertifier

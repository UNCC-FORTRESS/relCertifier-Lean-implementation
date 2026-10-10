/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The paper's left program for a mode-independent invariant: from a window choice to the
# guard-gated left automaton

The mode-keyed instances state Theorem 3 over the LEFT AUTOMATON `leftAutomatonBody A u_L`
(`ModeHandoff.lean`): `?(u_L = m') ; ⋃_{t ∈ next m'} ?guard_t ; u_L := t ; window_t`, the
paper's `cpsProg` body (jump, then flow). The mode-independent instances were first stated
over the plain choice of their windows, `bigChoice Ps`. This leaf is the generic bridge from
the second form to the first, proved once:

* `theorem3_leftAut_of_choice`: if `ψ = (ϕ ∧ env) ∧ Bk` is a Theorem 3 invariant for the
  left program `bigChoice Ps`, and every guard-gated left edge is a run of `bigChoice Ps`
  (`hsim`: from a state where `guard_t` holds, a run of `window_t` is a run of some member of
  `Ps`), then `psiK u_L (fun _ => ϕ) … Bk` (the same rows for every left mode, plus
  `u_L ∈ modes`) is a Theorem 3 invariant for the left automaton. The left automaton only
  REMOVES left runs (a declared successor, its guard tested, the window run) and adds the
  mode variable `u_L`, which the windows, the guards and `ψ`'s left side never read.

The proof is relational (bi-state semantics, `faShape`): a run of `L_A*` from `σ_L`, with
`u_L` reset to its start value, is a run of `(bigChoice Ps)*` (`leftStar_project`); the
given theorem answers it; `ψ`'s truth does not depend on the left `u_L`
(`rsat_congr_left`). No encoding of the NEW formula is needed, so `u_L` only has to be a
left variable the windows do not touch: the right state's mode variable may have the same
name (the bi-state keeps the two executions' states apart). This is what the `Var 2`
instances use (`u_L = (Aux, 0)` on the left, `mv = (Aux, 0)` on the right: `Var 2` has two
auxiliary slots per state, the left's clock takes the other).

* `hstep_modeKeyed_G`: the mode-keyed composition step with the entered mode's guard passed
  to the per-mode step (the guard is tested by the left edge before the window), for
  instances whose windows do not repeat the guard test.
* `LeftAut.ofG` / `LeftAut.ofP`: the left automaton from an instance's window data (guarded
  windows with their own guard, or plain windows with the IR guards), with `hsim` and the
  footprint facts proved once.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.GuardedSwitch

namespace RelCertifier
open DL DLCalTiming DLRel Set Function

variable {n : ℕ}

/-! ## Relational facts -/

/-- The bi-state truth of a formula with disjoint left/right footprints does not depend on
the left state outside the formula's left variables. -/
theorem rsat_congr_left (ψ : RFormula (Var n)) (hd : Disjoint ψ.varsL ψ.varsR)
    {a a' b : State (Var n)} (h : EqOn a a' ψ.varsL) :
    RFormula.sat ψ (a, b) ↔ RFormula.sat ψ (a', b) := by
  have hd' : Disjoint ψ.varsL (Equiv.refl (Var n) '' ψ.varsR) := by simpa using hd
  obtain ⟨σ, hσ⟩ := exists_bridge (Equiv.refl (Var n)) ψ.varsL ψ.varsR hd' (a, b)
  have hσ' : Bridges (Equiv.refl (Var n)) ψ.varsL ψ.varsR (a', b) σ :=
    ⟨fun x hx => (hσ.left hx).trans (h hx), hσ.right⟩
  rw [RFormula.encoding_correct _ ψ hd' (a, b) σ hσ,
    RFormula.encoding_correct _ ψ hd' (a', b) σ hσ']

/-- The ∀∃ shape at a bi-state, unfolded. -/
theorem rsat_faShape_iff (α β : Program (Var n)) (ψ : RFormula (Var n)) (a b : State (Var n)) :
    RFormula.sat (faShape α β ψ) (a, b) ↔
      ∀ a', Program.sem α a a' → ∃ b', Program.sem β b b' ∧ RFormula.sat ψ (a', b') := by
  classical
  simp only [faShape, RFormula.rdiamond, RFormula.sat, Prod.forall, RProgram.sem]
  have htt : ∀ s s' : State (Var n), Program.sem (Program.test Formula.tt) s s' ↔ s = s' := by
    intro s s'; simp [Program.sem, Formula.sat]
  constructor
  · intro h a' ha'
    have h1 := h a' b ⟨ha', (htt b b).mpr rfl⟩
    push_neg at h1
    obtain ⟨x, y, ⟨hx, hy⟩, hs⟩ := h1
    rw [htt] at hx
    subst hx
    exact ⟨y, hy, hs⟩
  · rintro h a' b' ⟨ha', hb'⟩ hcon
    rw [htt] at hb'
    subst hb'
    obtain ⟨y, hy, hs⟩ := h a' ha'
    exact hcon a' y ⟨(htt a' a').mpr rfl, hy⟩ hs

theorem rsat_rbigAnd {fs : List (RFormula (Var n))} {bs : BiState (Var n)} :
    RFormula.sat (rbigAnd fs) bs ↔ ∀ f ∈ fs, RFormula.sat f bs := by
  induction fs with
  | nil => simp [rbigAnd, RFormula.tt, Formula.sat]
  | cons a as ih =>
      simp only [rbigAnd, RFormula.sat, ih, List.mem_cons, forall_eq_or_imp]

theorem rsat_modeKeyedR {ul : Var n} {ϕ : ℕ → RFormula (Var n)} {nL : ℕ}
    {bs : BiState (Var n)} :
    RFormula.sat (modeKeyedR ul ϕ nL) bs ↔
      ∀ m < nL, bs.1 ul = (m : ℝ) → RFormula.sat (ϕ m) bs := by
  unfold modeKeyedR
  rw [rsat_rbigAnd]
  constructor
  · intro h m hm hul
    have := h _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)
    rw [RFormula_sat_imp] at this
    exact this (sat_modeIs.mpr hul)
  · intro h f hf
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hf
    rw [RFormula_sat_imp]
    intro hul
    exact h m (List.mem_range.mp hm) (sat_modeIs.mp hul)

/-! ## Projecting left-automaton runs onto window-choice runs -/

/-- A program that never mentions `ul` commutes with resetting `ul`. -/
theorem sem_reset {P : Program (Var n)} {ul : Var n} (hP : ul ∉ Program.vars P)
    {s s' : State (Var n)} (c : ℝ) (h : Program.sem P s s') :
    Program.sem P (update s ul c) (update s' ul c) := by
  classical
  have hfv : P.fv ⊆ {x | x ≠ ul} := fun x hx hxe => hP (Or.inl (hxe ▸ hx))
  have hag : EqOn s (update s ul c) {x | x ≠ ul} :=
    fun x hx => (update_of_ne hx _ _).symm
  obtain ⟨ω₂, hrun, heq⟩ := Program.coincidence P hfv hag h
  have hω₂ : ω₂ = update s' ul c := by
    funext x
    by_cases hx : x = ul
    · subst hx
      rw [update_self]
      have := Program.bound_effect P hrun x (fun hb => hP (Or.inr hb))
      rw [← this, update_self]
    · rw [update_of_ne hx]; exact (heq (Or.inl hx)).symm
  rw [← hω₂]; exact hrun

/-- One left-automaton step, with `u_L` reset to `c` at both ends, is a run of `Lold`; and
it ends with `u_L` a declared mode. -/
theorem leftStep_project (A : LeftAut n) (ul : Var n) (Lold : Program (Var n))
    (hulW : ∀ t < A.numModes, ul ∉ Program.vars (A.window t))
    (hulG : ∀ t < A.numModes, ul ∉ (A.guard t).fv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hsim : ∀ t < A.numModes, ∀ σ ν, Formula.sat (A.guard t) σ →
      Program.sem (A.window t) σ ν → Program.sem Lold σ ν)
    (c : ℝ) {s s' : State (Var n)} (h : Program.sem (leftAutomatonBody A ul) s s') :
    Program.sem Lold (update s ul c) (update s' ul c) ∧ ∃ t < A.numModes, s' ul = (t : ℝ) := by
  classical
  obtain ⟨p, hp, hsemp⟩ := bigChoiceP_sem_forward h
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨m', hm', rfl⟩ := hp
  obtain ⟨σ₁, ⟨hσ₁, _⟩, hrest⟩ := hsemp
  subst hσ₁
  obtain ⟨p₂, hp₂, hsem₂⟩ := bigChoiceP_sem_forward hrest
  simp only [List.mem_map] at hp₂
  obtain ⟨t, ht, rfl⟩ := hp₂
  obtain ⟨σ₂, ⟨hσ₂, hguard⟩, σ₃, hassign, hwin⟩ := hsem₂
  subst hσ₂
  have ht' : t < A.numModes := hnext m' hm' t ht
  have hσ₃ : σ₃ = update s ul (t : ℝ) := by
    funext x
    by_cases hx : x = ul
    · subst hx
      rw [update_self]
      simpa [Term.eval] using hassign.1
    · rw [update_of_ne hx]
      exact hassign.2 x hx
  subst hσ₃
  refine ⟨?_, t, ht', ?_⟩
  · have hrun := sem_reset (hulW t ht') c hwin
    rw [update_idem] at hrun
    have hg : Formula.sat (A.guard t) (update s ul c) :=
      (Formula.coincidence (A.guard t) (fun y hy =>
        (update_of_ne (fun hc => hulG t ht' (by rw [← hc]; exact hy)) _ _).symm)).mp hguard
    exact hsim t ht' _ _ hg hrun
  · have := Program.bound_effect (A.window t) hwin ul (fun hb => hulW t ht' (Or.inr hb))
    rw [← this, update_self]

/-- The star of the left automaton projects onto the star of `Lold` (with `u_L` reset), and
`u_L` either kept its start value or holds a declared mode. -/
theorem leftStar_project (A : LeftAut n) (ul : Var n) (Lold : Program (Var n))
    (hulW : ∀ t < A.numModes, ul ∉ Program.vars (A.window t))
    (hulG : ∀ t < A.numModes, ul ∉ (A.guard t).fv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hsim : ∀ t < A.numModes, ∀ σ ν, Formula.sat (A.guard t) σ →
      Program.sem (A.window t) σ ν → Program.sem Lold σ ν)
    (c : ℝ) {s s' : State (Var n)}
    (h : Relation.ReflTransGen (Program.sem (leftAutomatonBody A ul)) s s') :
    Relation.ReflTransGen (Program.sem Lold) (update s ul c) (update s' ul c) ∧
      (s' ul = s ul ∨ ∃ t < A.numModes, s' ul = (t : ℝ)) := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, Or.inl rfl⟩
  | tail _ hstep ih =>
      obtain ⟨hrun, hmode⟩ := leftStep_project A ul Lold hulW hulG hnext hsim c hstep
      exact ⟨ih.1.tail hrun, Or.inr hmode⟩

/-! ## The bridge -/

/-- **From the window choice to the left automaton.** A Theorem 3 invariant
`(ϕ ∧ env) ∧ Bk` for the left program `bigChoice Ps` (here any `Lold`) gives the
mode-independent mode-keyed invariant `psiK u_L (fun _ => ϕ) …` for the guard-gated left
automaton, provided every left edge (the entered mode's guard holds, then its window runs)
is a run of `Lold`, and `u_L` is not read by the windows, the guards or `ψ`'s left side. -/
theorem theorem3_leftAut_of_choice (A : LeftAut n) (ul : Var n) (Lold R : Program (Var n))
    (ϕ : RFormula (Var n)) (domL domR : Formula (Var n)) (BkR : RFormula (Var n))
    (hold : RFormula.rvalid (theorem3Form Lold R
      (RFormula.and (RFormula.and ϕ (envLR domL domR)) BkR)))
    (hdψ : Disjoint (RFormula.and (RFormula.and ϕ (envLR domL domR)) BkR).varsL
      (RFormula.and (RFormula.and ϕ (envLR domL domR)) BkR).varsR)
    (hulψ : ul ∉ (RFormula.and (RFormula.and ϕ (envLR domL domR)) BkR).varsL)
    (hulW : ∀ t < A.numModes, ul ∉ Program.vars (A.window t))
    (hulG : ∀ t < A.numModes, ul ∉ (A.guard t).fv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hsim : ∀ t < A.numModes, ∀ σ ν, Formula.sat (A.guard t) σ →
      Program.sem (A.window t) σ ν → Program.sem Lold σ ν) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody A ul) R
      (psiK ul (fun _ => ϕ) A.numModes domL domR BkR)) := by
  classical
  set ψ := RFormula.and (RFormula.and ϕ (envLR domL domR)) BkR with hψ
  rintro ⟨a, b⟩
  rw [theorem3Form, RFormula_sat_imp]
  intro hpre
  obtain ⟨⟨⟨hMK, henv⟩, hBk⟩, hul⟩ := hpre
  have hulv : Formula.sat (mvValid ul A.numModes) a := hul
  obtain ⟨m0, hm0, ha0⟩ := sat_mvValid.mp hulv
  have hϕ : RFormula.sat ϕ (a, b) := rsat_modeKeyedR.mp hMK m0 hm0 ha0
  have hψa : RFormula.sat ψ (a, b) := ⟨⟨hϕ, henv⟩, hBk⟩
  have hfa := (RFormula_sat_imp _ _ _).mp (hold (a, b)) hψa
  rw [rsat_faShape_iff] at hfa ⊢
  intro a' hrun
  obtain ⟨hrunO, hmode⟩ := leftStar_project A ul Lold hulW hulG hnext hsim (a ul) hrun
  rw [update_eq_self] at hrunO
  obtain ⟨b', hb', hψ'⟩ := hfa _ hrunO
  have hψ'' : RFormula.sat ψ (a', b') := by
    refine (rsat_congr_left ψ hdψ (a := update a' ul (a ul)) (a' := a') ?_).mp hψ'
    intro x hx
    have hxu : x ≠ ul := fun h => hulψ (h ▸ hx)
    exact update_of_ne hxu _ _
  obtain ⟨⟨hϕ', henv'⟩, hBk'⟩ := hψ''
  refine ⟨b', hb', ⟨⟨?_, henv'⟩, hBk'⟩, ?_⟩
  · exact rsat_modeKeyedR.mpr (fun _ _ _ => hϕ')
  · show Formula.sat (mvValid ul A.numModes) a'
    rw [sat_mvValid]
    rcases hmode with h | ⟨t, ht, h⟩
    · exact ⟨m0, hm0, h.trans ha0⟩
    · exact ⟨t, ht, h⟩

/-! ## The left automaton from an instance's window data -/

/-- Guarded windows (each begins with its own guard test, as `gwindowSeg`), the guards the
same list's first components, the declared successors `next`. -/
noncomputable def LeftAut.ofG
    (data : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (tg : Var n) (dt : ℝ) (next : List (List ℕ)) : LeftAut n :=
  { windows := data.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2),
    guards := data.map (fun d => d.1),
    next := next }

/-- Plain clock-capped windows, with the lowered IR guards supplied separately (tested by
the left edge only). -/
noncomputable def LeftAut.ofP
    (data : List ((Fin n → Term (Var n)) × Formula (Var n) × ℕ)) (guards : List (Formula (Var n)))
    (tg : Var n) (dt : ℝ) (next : List (List ℕ)) : LeftAut n :=
  { windows := data.map (fun d => windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2),
    guards := guards,
    next := next }

theorem LeftAut.ofG_numModes data (tg : Var n) dt next :
    (LeftAut.ofG data tg dt next).numModes = data.length := by
  simp [LeftAut.ofG, LeftAut.numModes]

theorem LeftAut.ofP_numModes data guards (tg : Var n) dt next :
    (LeftAut.ofP data guards tg dt next).numModes = data.length := by
  simp [LeftAut.ofP, LeftAut.numModes]

theorem sem_bigChoice_of_mem {ps : List (Program (Var n))} {p : Program (Var n)}
    (hp : p ∈ ps) {σ ν : State (Var n)} (h : Program.sem p σ ν) :
    Program.sem (bigChoice ps) σ ν := by
  induction ps with
  | nil => exact absurd hp (by simp)
  | cons a as ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl h
      · exact Or.inr (ih hp)

theorem LeftAut.ofG_window_mem data (tg : Var n) dt next (t : ℕ) (ht : t < data.length) :
    (LeftAut.ofG data tg dt next).window t ∈
      data.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2) := by
  simp only [LeftAut.window, LeftAut.ofG]
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  exact List.getElem_mem _

theorem LeftAut.ofP_window_mem data guards (tg : Var n) dt next (t : ℕ) (ht : t < data.length) :
    (LeftAut.ofP data guards tg dt next).window t ∈
      data.map (fun d => windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2) := by
  simp only [LeftAut.window, LeftAut.ofP]
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  exact List.getElem_mem _

theorem LeftAut.ofG_hsim data (tg : Var n) dt next :
    ∀ t < (LeftAut.ofG data tg dt next).numModes, ∀ σ ν,
      Formula.sat ((LeftAut.ofG data tg dt next).guard t) σ →
      Program.sem ((LeftAut.ofG data tg dt next).window t) σ ν →
      Program.sem (bigChoice (data.map (fun d =>
        gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2))) σ ν := by
  intro t ht σ ν _ h
  rw [LeftAut.ofG_numModes] at ht
  exact sem_bigChoice_of_mem (LeftAut.ofG_window_mem data tg dt next t ht) h

theorem LeftAut.ofP_hsim data guards (tg : Var n) dt next :
    ∀ t < (LeftAut.ofP data guards tg dt next).numModes, ∀ σ ν,
      Formula.sat ((LeftAut.ofP data guards tg dt next).guard t) σ →
      Program.sem ((LeftAut.ofP data guards tg dt next).window t) σ ν →
      Program.sem (bigChoice (data.map (fun d =>
        windowSeg (leftBlock d.1) d.2.1 tg dt d.2.2))) σ ν := by
  intro t ht σ ν _ h
  rw [LeftAut.ofP_numModes] at ht
  exact sem_bigChoice_of_mem (LeftAut.ofP_window_mem data guards tg dt next t ht) h

/-- The guarded windows and their guards read only `tg = (Aux, b)` and left coordinates. -/
theorem LeftAut.ofG_vars data (b : Fin n) dt next
    (hL : ∀ d ∈ data, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
      d.2.2.1.fv ⊆ range Lv) :
    (∀ t < (LeftAut.ofG data ((Side.Aux, b) : Var n) dt next).numModes,
      Program.vars ((LeftAut.ofG data ((Side.Aux, b) : Var n) dt next).window t)
        ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv) ∧
    (∀ t < (LeftAut.ofG data ((Side.Aux, b) : Var n) dt next).numModes,
      ((LeftAut.ofG data ((Side.Aux, b) : Var n) dt next).guard t).fv ⊆ range Lv) := by
  constructor
  · intro t ht
    rw [LeftAut.ofG_numModes] at ht
    simp only [LeftAut.window, LeftAut.ofG]
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    have hd := hL _ (List.getElem_mem ht)
    exact vars_gwindowSegL_sub _ _ _ b dt _ hd.1 hd.2.1 hd.2.2
  · intro t ht
    rw [LeftAut.ofG_numModes] at ht
    simp only [LeftAut.guard, LeftAut.ofG]
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    exact (hL _ (List.getElem_mem ht)).1

theorem LeftAut.ofP_vars data guards (b : Fin n) dt next
    (hL : ∀ d ∈ data, (∀ i, (d.1 i).fv ⊆ range Lv) ∧ d.2.1.fv ⊆ range Lv)
    (hG : ∀ g ∈ guards, g.fv ⊆ range Lv) :
    (∀ t < (LeftAut.ofP data guards ((Side.Aux, b) : Var n) dt next).numModes,
      Program.vars ((LeftAut.ofP data guards ((Side.Aux, b) : Var n) dt next).window t)
        ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv) ∧
    (∀ t, ((LeftAut.ofP data guards ((Side.Aux, b) : Var n) dt next).guard t).fv
        ⊆ range Lv) := by
  constructor
  · intro t ht
    rw [LeftAut.ofP_numModes] at ht
    simp only [LeftAut.window, LeftAut.ofP]
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    have hd := hL _ (List.getElem_mem ht)
    exact vars_windowSegL_sub _ _ b dt _ hd.1 hd.2
  · intro t
    simp only [LeftAut.guard, LeftAut.ofP]
    by_cases ht : t < guards.length
    · rw [List.getD_eq_getElem _ _ ht]
      exact hG _ (List.getElem_mem ht)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [Formula.fv]

/-- The declared successors stay in range (checked on the literal `next` lists). -/
theorem LeftAut.ofG_hnext data (tg : Var n) dt (next : List (List ℕ)) (K : ℕ)
    (hk : data.length = K) (h : ∀ l ∈ next, ∀ t ∈ l, t < K) :
    ∀ m' < (LeftAut.ofG data tg dt next).numModes,
      ∀ t ∈ (LeftAut.ofG data tg dt next).succ m', t < (LeftAut.ofG data tg dt next).numModes := by
  intro m' _ t ht
  rw [LeftAut.ofG_numModes, hk]
  simp only [LeftAut.succ, LeftAut.ofG] at ht
  by_cases hm : m' < next.length
  · rw [List.getD_eq_getElem _ _ hm] at ht
    exact h _ (List.getElem_mem hm) t ht
  · rw [List.getD_eq_default _ _ (by omega)] at ht
    simp at ht

theorem LeftAut.ofP_hnext data guards (tg : Var n) dt (next : List (List ℕ)) (K : ℕ)
    (hk : data.length = K) (h : ∀ l ∈ next, ∀ t ∈ l, t < K) :
    ∀ m' < (LeftAut.ofP data guards tg dt next).numModes,
      ∀ t ∈ (LeftAut.ofP data guards tg dt next).succ m',
        t < (LeftAut.ofP data guards tg dt next).numModes := by
  intro m' _ t ht
  rw [LeftAut.ofP_numModes, hk]
  simp only [LeftAut.succ, LeftAut.ofP] at ht
  by_cases hm : m' < next.length
  · rw [List.getD_eq_getElem _ _ hm] at ht
    exact h _ (List.getElem_mem hm) t ht
  · rw [List.getD_eq_default _ _ (by omega)] at ht
    simp at ht

/-- Guarded-window data whose own guard component is not the IR guard (`⊤` in the carried-over
ladder modules), with the lowered IR guards supplied separately: the window list is the
choice program's, the guards are the file's. -/
noncomputable def LeftAut.ofGI
    (data : List (Formula (Var n) × (Fin n → Term (Var n)) × Formula (Var n) × ℕ))
    (guards : List (Formula (Var n))) (tg : Var n) (dt : ℝ) (next : List (List ℕ)) : LeftAut n :=
  { windows := data.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2),
    guards := guards,
    next := next }

theorem LeftAut.ofGI_numModes data guards (tg : Var n) dt next :
    (LeftAut.ofGI data guards tg dt next).numModes = data.length := by
  simp [LeftAut.ofGI, LeftAut.numModes]

theorem LeftAut.ofGI_hsim data guards (tg : Var n) dt next :
    ∀ t < (LeftAut.ofGI data guards tg dt next).numModes, ∀ σ ν,
      Formula.sat ((LeftAut.ofGI data guards tg dt next).guard t) σ →
      Program.sem ((LeftAut.ofGI data guards tg dt next).window t) σ ν →
      Program.sem (bigChoice (data.map (fun d =>
        gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2))) σ ν := by
  intro t ht σ ν _ h
  rw [LeftAut.ofGI_numModes] at ht
  have hmem : (LeftAut.ofGI data guards tg dt next).window t ∈
      data.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2) := by
    simp only [LeftAut.window, LeftAut.ofGI]
    rw [List.getD_eq_getElem _ _ (by simpa using ht)]
    exact List.getElem_mem _
  exact sem_bigChoice_of_mem hmem h

theorem LeftAut.ofGI_vars data guards (b : Fin n) dt next
    (hL : ∀ d ∈ data, d.1.fv ⊆ range Lv ∧ (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧
      d.2.2.1.fv ⊆ range Lv)
    (hG : ∀ g ∈ guards, g.fv ⊆ range Lv) :
    (∀ t < (LeftAut.ofGI data guards ((Side.Aux, b) : Var n) dt next).numModes,
      Program.vars ((LeftAut.ofGI data guards ((Side.Aux, b) : Var n) dt next).window t)
        ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv) ∧
    (∀ t, ((LeftAut.ofGI data guards ((Side.Aux, b) : Var n) dt next).guard t).fv
        ⊆ range Lv) := by
  constructor
  · intro t ht
    rw [LeftAut.ofGI_numModes] at ht
    simp only [LeftAut.window, LeftAut.ofGI]
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]
    have hd := hL _ (List.getElem_mem ht)
    exact vars_gwindowSegL_sub _ _ _ b dt _ hd.1 hd.2.1 hd.2.2
  · intro t
    simp only [LeftAut.guard, LeftAut.ofGI]
    by_cases ht : t < guards.length
    · rw [List.getD_eq_getElem _ _ ht]
      exact hG _ (List.getElem_mem ht)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [Formula.fv]

theorem LeftAut.ofGI_hnext data guards (tg : Var n) dt (next : List (List ℕ)) (K : ℕ)
    (hk : data.length = K) (h : ∀ l ∈ next, ∀ t ∈ l, t < K) :
    ∀ m' < (LeftAut.ofGI data guards tg dt next).numModes,
      ∀ t ∈ (LeftAut.ofGI data guards tg dt next).succ m',
        t < (LeftAut.ofGI data guards tg dt next).numModes := by
  intro m' _ t ht
  rw [LeftAut.ofGI_numModes, hk]
  simp only [LeftAut.succ, LeftAut.ofGI] at ht
  by_cases hm : m' < next.length
  · rw [List.getD_eq_getElem _ _ hm] at ht
    exact h _ (List.getElem_mem hm) t ht
  · rw [List.getD_eq_default _ _ (by omega)] at ht
    simp at ht

/-- **The bridge in the instances' vocabulary.** `mv = (Aux, a)` (right), the left clock
`tg = (Aux, b)`, `u_L = (Aux, c)` with `c ≠ b` (`c = a` is allowed: different executions).
The invariant's rows read left and right coordinates, the envelope and the right region
read their own side. -/
theorem theorem3_leftAut_of_choiceR (A : LeftAut n) (a b c : Fin n) (hcb : c ≠ b)
    (Lold R : Program (Var n)) (ϕ : RFormula (Var n)) (domL domR : Formula (Var n))
    (regions : ℕ → Formula (Var n)) (k : ℕ)
    (hold : RFormula.rvalid (theorem3Form Lold R
      (RFormula.and (RFormula.and ϕ (envLR domL domR))
        (mvRegionR ((Side.Aux, a) : Var n) regions k))))
    (hreg : ∀ q < k, (regions q).fv ⊆ range Rv)
    (hinvL : ϕ.varsL ⊆ range Lv) (hinvR : ϕ.varsR ⊆ range Rv)
    (hdomLv : domL.fv ⊆ range Lv) (hdomRv : domR.fv ⊆ range Rv)
    (hwin : ∀ t < A.numModes, Program.vars (A.window t) ⊆ {((Side.Aux, b) : Var n)} ∪ range Lv)
    (hgrd : ∀ t < A.numModes, (A.guard t).fv ⊆ range Lv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hsim : ∀ t < A.numModes, ∀ σ ν, Formula.sat (A.guard t) σ →
      Program.sem (A.window t) σ ν → Program.sem Lold σ ν) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody A ((Side.Aux, c) : Var n)) R
      (psiK ((Side.Aux, c) : Var n) (fun _ => ϕ) A.numModes domL domR
        (mvRegionR ((Side.Aux, a) : Var n) regions k))) := by
  have hL : (RFormula.and (RFormula.and ϕ (envLR domL domR))
      (mvRegionR ((Side.Aux, a) : Var n) regions k)).varsL ⊆ range Lv := by
    intro v hv
    rcases ψmultiR_varsL_sub _ regions k ϕ domL domR hv with hv | hv
    · exact hinvL hv
    · exact hdomLv hv
  have hR : (RFormula.and (RFormula.and ϕ (envLR domL domR))
      (mvRegionR ((Side.Aux, a) : Var n) regions k)).varsR
        ⊆ {((Side.Aux, a) : Var n)} ∪ range Rv := by
    intro v hv
    rcases ψmultiR_varsR_sub _ regions k ϕ domL domR hreg hv with (hv | hv) | (hv | hv)
    · exact Or.inr (hinvR hv)
    · exact Or.inr (hdomRv hv)
    · exact Or.inl hv
    · exact Or.inr hv
  refine theorem3_leftAut_of_choice A _ Lold R ϕ domL domR _ hold ?_ ?_ ?_ ?_ hnext hsim
  · rw [Set.disjoint_left]
    intro x hxL hxR
    obtain ⟨i, rfl⟩ := hL hxL
    rcases hR hxR with h | ⟨j, hj⟩
    · exact absurd (Set.mem_singleton_iff.mp h) (by simp [Lv, Prod.ext_iff])
    · exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
  · intro h
    obtain ⟨i, hi⟩ := hL h
    exact absurd hi (by simp [Lv, Prod.ext_iff])
  · intro t ht h
    rcases hwin t ht h with h | ⟨i, hi⟩
    · exact hcb (by simpa [Prod.ext_iff] using Set.mem_singleton_iff.mp h)
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
  · intro t ht h
    obtain ⟨i, hi⟩ := hgrd t ht h
    exact absurd hi (by simp [Lv, Prod.ext_iff])

/-! ## The mode-keyed step with the guard passed to the per-mode step -/

/-- `hstep_modeKeyed` with the entered mode's guard available to the per-mode step (it is
tested by the left edge at the switch state, and `u_L` does not occur in it). -/
theorem hstep_modeKeyed_G (A : LeftAut n) (ul : Var n) (R : Program (Var n))
    (F : ℕ → Formula (Var n)) (env Bk : Formula (Var n))
    (hulF : ∀ m, ul ∉ (F m).fv) (hulenv : ul ∉ env.fv) (hulBk : ul ∉ Bk.fv)
    (hulG : ∀ t, ul ∉ (A.guard t).fv)
    (hframes : ∀ t, FramesMv (A.window t) ul)
    (hulR : ul ∉ R.bv)
    (hnext : ∀ m' < A.numModes, ∀ t ∈ A.succ m', t < A.numModes)
    (hstepM : ∀ t < A.numModes, ∀ σ, Formula.sat (A.guard t) σ →
      Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (A.window t) (Program.star R)
        (Formula.and (Formula.and (F t) env) Bk)) σ)
    (hhand : ∀ m' < A.numModes, ∀ t ∈ A.succ m', ∀ ω,
      Formula.sat (F m') ω → Formula.sat env ω → Formula.sat (A.guard t) ω →
      Formula.sat (F t) ω) :
    ∀ σ, Formula.sat (phiInvK ul F A.numModes env Bk) σ →
      Formula.sat (faModal (Equiv.refl (Var n)) (leftAutomatonBody A ul) (Program.star R)
        (phiInvK ul F A.numModes env Bk)) σ := by
  intro σ hσ
  obtain ⟨⟨⟨hMK, henv⟩, hBk⟩, hul⟩ := hσ
  obtain ⟨m', hm', hulm'⟩ := sat_mvValid.mp hul
  rw [faModal_sat]
  intro ν hleft
  obtain ⟨p, hp, hsemp⟩ := bigChoiceP_sem_forward hleft
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨m'', _, rfl⟩ := hp
  obtain ⟨σ₁, ⟨hσ₁, htest⟩, hrest⟩ := hsemp
  subst hσ₁
  have hm''eq : m'' = m' := by
    have h1 : σ ul = (m'' : ℝ) := sat_modeIs.mp htest
    exact_mod_cast h1.symm.trans hulm'
  subst hm''eq
  obtain ⟨p₂, hp₂, hsem₂⟩ := bigChoiceP_sem_forward hrest
  simp only [List.mem_map] at hp₂
  obtain ⟨t, ht, rfl⟩ := hp₂
  obtain ⟨σ₂, ⟨hσ₂, hguard⟩, σ₃, hassign, hwin⟩ := hsem₂
  subst hσ₂
  have ht' : t < A.numModes := hnext m'' hm' t ht
  have hσ₃ : σ₃ = Function.update σ ul (t : ℝ) := by
    funext x
    by_cases hx : x = ul
    · subst hx
      rw [Function.update_self]
      simpa [Term.eval] using hassign.1
    · rw [Function.update_of_ne hx]
      exact hassign.2 x hx
  have hFm' : Formula.sat (F m'') σ := (sat_modeKeyed.mp hMK) m'' hm' hulm'
  have hFt : Formula.sat (F t) σ := hhand m'' hm' t ht σ hFm' henv hguard
  have hcoin : ∀ (G : Formula (Var n)), ul ∉ G.fv →
      (Formula.sat G σ₃ ↔ Formula.sat G σ) := by
    intro G hG
    rw [hσ₃]
    exact (Formula.coincidence G (fun y hy =>
      (Function.update_of_ne (fun hc => hG (by rw [← hc]; exact hy)) _ _).symm)).symm
  have hσ₃sat : Formula.sat (Formula.and (Formula.and (F t) env) Bk) σ₃ :=
    ⟨⟨(hcoin _ (hulF t)).mpr hFt, (hcoin _ hulenv).mpr henv⟩, (hcoin _ hulBk).mpr hBk⟩
  have hfa := hstepM t ht' σ₃ ((hcoin _ (hulG t)).mpr hguard) hσ₃sat
  rw [faModal_sat] at hfa
  obtain ⟨μ, hRμ, ⟨hFtμ, henvμ⟩, hBkμ⟩ := hfa ν hwin
  refine ⟨μ, hRμ, ?_⟩
  have hulμ : μ ul = (t : ℝ) := by
    have h1 : ν ul = σ₃ ul := hframes t σ₃ ν hwin
    rw [Program.rename_refl] at hRμ
    have h2 : ν ul = μ ul :=
      Program.bound_effect (Program.star R) hRμ ul (by simpa [Program.bv] using hulR)
    rw [← h2, h1, hσ₃, Function.update_self]
  refine ⟨⟨⟨?_, henvμ⟩, hBkμ⟩, ?_⟩
  · rw [sat_modeKeyed]
    intro m _ hμm
    have hmt : m = t := by exact_mod_cast hμm.symm.trans hulμ
    subst hmt
    exact hFtμ
  · rw [sat_mvValid]
    exact ⟨t, ht', hulμ⟩

end RelCertifier

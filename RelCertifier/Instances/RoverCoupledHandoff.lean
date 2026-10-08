/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_coupled` — the DECLARED mode-dependent invariant, composed across left switches

`RoverCoupledModal.rover_coupled_modal` states Theorem 3 at the weakest declared row
(`Stop`, offset 2) for every left window. This leaf states what the file declares: one
row per LEFT mode (`Drive` 0.5, `Drift` 1.0, `Stop` 2.0), keyed by the left mode variable
`u_L = (Aux, 2)`, as a ∀∃ invariant of the full left automaton over the file's `next`
lists. Ingredients:

* a per-left-mode step at that mode's own row (`HmultiRow` — the catch-up response of the
  base instance, which is offset-independent: a Safe hold of `8·dt` regains `≥ 2·dt`
  while the left window gains `≤ 2·dt`);
* the handoff at every declared transition, in-kernel: the rows are nested constant
  offsets (`0.5 ≤ 1.0 ≤ 2.0`), so `linarith` closes each (the tool's handoff check
  reports 5/5 `unsat`; `docs/HANDOFF.md`).

Z3-free, like the base instance: `#print axioms` is the standard three.
-/
import RelCertifier.Instances.RoverCoupledModal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace RoverCoupledHandoff

open DL DLCalTiming DLRel Parse Set RoverCoupledModal

set_option maxHeartbeats 12800000

/-- The left mode variable — the third auxiliary coordinate (`mv = (Aux, 0)`, `tg = (Aux, 1)`). -/
abbrev ulC2 : Var 4 := (Side.Aux, 2)

/-! ## The declared rows, one per left mode -/

def invRowPF (r : ℕ) : Parse.PForm := (rover_coupled_IR.invariants.getD r ("", Parse.PForm.tt)).2

noncomputable def gRow (r : ℕ) : Term (Var 4) :=
  ((Run.invToG vsC2 4 ((atomsOf (invRowPF r)).getD 0 .tt)).map ITerm.toHost).getD (Term.const 0)

/-- Row `r`'s loop formula and its relational form (`canonInvM`, as every instance). -/
noncomputable def FRow (r : ℕ) : Formula (Var 4) := FM (gRow r) []
noncomputable def ϕRow (r : ℕ) : RFormula (Var 4) := canonInvM (gRow r) []

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 4)) (ϕRow r) = FRow r :=
  encode_canonInvM (gRow r) []

/-- The declared offsets. -/
noncomputable def cRow (r : ℕ) : ℝ := if r = 0 then 1/2 else if r = 1 then 1 else 2

theorem eval_gRow (r : ℕ) (hr : r < 3) (x : State (Var 4)) :
    Term.eval (gRow r) x = x (Lv 0) - (x (Rv 0) + cRow r) := by
  have hdL : ("L_px".drop 2).copy = "px" := by decide
  have hdR : ("R_px".drop 2).copy = "px" := by decide
  interval_cases r <;>
  · simp [gRow, atomsOf, invRowPF, rover_coupled_IR, Run.invToG, Run.lowerE, vsC2,
      Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hC205, hC210, hC220,
      ITerm.toHost, Term.eval, AOp.interp, Lv, Rv, cRow]

theorem hgRow (r : ℕ) : (gRow r).fv ⊆ range Lv ∪ range Rv := invToG_pipeline_LR _

theorem aux_notin_gRow (a : Fin 4) (r : ℕ) : ((Side.Aux, a) : Var 4) ∉ (gRow r).fv := by
  intro h
  rcases hgRow r h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

theorem aux_notin_FRow (a : Fin 4) (r : ℕ) : ((Side.Aux, a) : Var 4) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl; exact aux_notin_gRow a r)

theorem sat_FRow (r : ℕ) (hr : r < 3) (x : State (Var 4)) :
    Formula.sat (FRow r) x ↔ x (Lv 0) ≤ x (Rv 0) + cRow r := by
  unfold FRow
  rw [sat_FM_iff]
  constructor
  · intro h
    have := h (gRow r) List.mem_cons_self
    rw [eval_gRow r hr] at this; linarith
  · intro h g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'; rw [eval_gRow r hr]; linarith

/-! ## The per-left-mode step at the mode's own row (the base instance's catch-up
response, with the offset generalized) -/

theorem HmultiRow (r : ℕ) (hr : r < 3) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∀ (q : ℕ), q < GrC2.modes.length → ∀ σ, σ mvC2 = (q : ℝ) →
      Formula.sat (Formula.and (FRow r) envC2) σ →
      ∃ segs : List (ℕ × RMode (Var 4) × REdge (Var 4)),
        (∀ s ∈ segs, GrC2.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ GrC2.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 4))
          (windowSeg (leftBlock (fLC2 r)) domLC2 tgC2 dt 2)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (FRow r) envC2)) σ := by
  intro q hq σ hmv hσ
  have hq3 : q < 3 := by simpa [GrC2] using hq
  have hφ : σ (Lv 0) ≤ σ (Rv 0) + cRow r := (sat_FRow r hr σ).mp hσ.1
  have hdomRσ : Formula.sat domRC2 σ := hσ.2.2
  have hRb := (sat_domRC2 σ).mp hdomRσ
  have hchain2 : ∀ (a b c : ℕ × RMode (Var 4) × REdge (Var 4)),
      a.2.2.tgt = b.1 → b.2.2.tgt = c.1 →
      List.IsChain (fun x y => x.2.2.tgt = y.1) [a, b, c] := by
    intro a b c hab hbc
    refine (List.isChain_cons.mpr ⟨?_, ?_⟩)
    · intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hab
    · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; exact hbc
  -- the faModal body, shared by all starts: the right survives the window,
  -- hops (zero-duration) to Safe, holds for 8·dt
  have hbody : ∀ (pres : List (Program (Var 4))),
      (∀ Q ∈ pres, ∀ μ : State (Var 4), Formula.sat domRC2 μ →
        Program.sem Q μ μ) →
      Formula.sat (faModal (Equiv.refl (Var 4))
        (windowSeg (leftBlock (fLC2 r)) domLC2 tgC2 dt 2)
        (bigSeq (pres ++ [Program.ode (rightBlock (fRC2 2) (Term.const 1)) domRC2]))
        (Formula.and (FRow r) envC2)) σ := by
    intro pres hpres
    rw [faModal_sat]
    intro ν hleft
    have hpx := window_pxL_bound r hr dt hdt 2 hleft
    push_cast at hpx
    have hmaskν := window_maskC2 r dt 2 hleft
    have hdomLν := windowSeg_end_domL (leftBlock (fLC2 r)) domLC2 tgC2 dt 2
      (by norm_num) hleft
    have hdomRν : Formula.sat domRC2 ν := by
      rw [sat_domRC2]
      rw [hmaskν 0, hmaskν 2, hmaskν 3]
      exact (sat_domRC2 σ).mp hdomRσ
    set τ : ℝ := 8 * dt with hτdef
    have hτ : 0 ≤ τ := by positivity
    have hhold := sem_safe_hold τ hτ hdomRν
    set μfin : State (Var 4) :=
      (fun x => if x = Rv 0 then ν (Rv 0) + ν (Rv 2) * τ
        else if x = Rv 1 then ν (Rv 1) + ν (Rv 3) * τ else ν x) with hμfin
    have hsemseq : Program.sem
        (bigSeq (pres ++ [Program.ode (rightBlock (fRC2 2) (Term.const 1)) domRC2]))
        ν μfin := by
      clear hpx
      induction pres with
      | nil =>
          simp only [List.nil_append, bigSeq]
          exact ⟨μfin, hhold, by rw [sem_test]; exact ⟨rfl, trivial⟩⟩
      | cons Q rest ih =>
          simp only [List.cons_append, bigSeq]
          refine ⟨ν, hpres Q List.mem_cons_self ν hdomRν, ?_⟩
          exact ih (fun Q' hQ' => hpres Q' (List.mem_cons_of_mem _ hQ'))
    refine ⟨μfin, by rw [Program.rename_refl]; exact hsemseq, ?_, ?_⟩
    · -- the invariant at the endpoint: catch-up arithmetic, offset-independent
      rw [sat_FRow r hr]
      have hν0 : μfin (Lv 0) = ν (Lv 0) := by
        simp [hμfin,
          if_neg (show (Lv 0 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
          if_neg (show (Lv 0 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
      have hνR : μfin (Rv 0) = ν (Rv 0) + ν (Rv 2) * τ := by simp [hμfin]
      rw [hν0, hνR]
      have hvfloor : (1:ℝ)/4 ≤ ν (Rv 2) := by
        rw [hmaskν 2]; exact hRb.2.1
      have hgain : 2 * dt ≤ ν (Rv 2) * τ := by
        rw [hτdef]
        nlinarith
      have hRν : ν (Rv 0) = σ (Rv 0) := hmaskν 0
      rw [hRν]
      linarith
    · constructor
      · have : Formula.sat domLC2 μfin := by
          rw [sat_domLC2]
          have h0 : μfin (Lv 0) = ν (Lv 0) := by
            simp [hμfin,
              if_neg (show (Lv 0 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
              if_neg (show (Lv 0 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
          have h1 : μfin (Lv 1) = ν (Lv 1) := by
            simp [hμfin,
              if_neg (show (Lv 1 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
              if_neg (show (Lv 1 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
          have h2 : μfin (Lv 2) = ν (Lv 2) := by
            simp [hμfin,
              if_neg (show (Lv 2 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
              if_neg (show (Lv 2 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
          have h3 : μfin (Lv 3) = ν (Lv 3) := by
            simp [hμfin,
              if_neg (show (Lv 3 : Var 4) ≠ Rv 0 by simp [Lv, Rv, Prod.ext_iff]),
              if_neg (show (Lv 3 : Var 4) ≠ Rv 1 by simp [Lv, Rv, Prod.ext_iff])]
          rw [h0, h1, h2, h3]
          exact (sat_domLC2 ν).mp hdomLν
        exact this
      · exact sem_ode_ends_in_domain hhold
  -- dispatch on the start mode: zero-hops up the chain, hold in Safe
  interval_cases q
  · refine ⟨[(0, modeC2 0, edgeC2 0 1), (1, modeC2 1, edgeC2 1 2), (2, modeC2 2, edgeC2 2 2)],
      ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact ⟨GrC2_modeAt 0 (by norm_num), edgeC2_mem 0 1 (by simp [GrC2])⟩
      · exact ⟨GrC2_modeAt 1 (by norm_num), edgeC2_mem 1 2 (by simp [GrC2])⟩
      · exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
    · exact hchain2 _ _ _ rfl rfl
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [Program.ode (rightBlock (fRC2 0) (Term.const 1)) domRC2,
        Program.ode (rightBlock (fRC2 1) (Term.const 1)) domRC2]
        (by
          intro Q hQ μ hdom
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl
          · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 0)
              (lam := Term.const 1) (domR := domRC2) hdom
            rwa [hρ] at hsem
          · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 1)
              (lam := Term.const 1) (domR := domRC2) hdom
            rwa [hρ] at hsem)
      simpa [modeC2] using this
  · refine ⟨[(1, modeC2 1, edgeC2 1 2), (2, modeC2 2, edgeC2 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact ⟨GrC2_modeAt 1 (by norm_num), edgeC2_mem 1 2 (by simp [GrC2])⟩
      · exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
    · refine (List.isChain_cons.mpr ⟨?_, by simp⟩)
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy; rfl
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [Program.ode (rightBlock (fRC2 1) (Term.const 1)) domRC2]
        (by
          intro Q hQ μ hdom
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
          subst hQ
          obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fRC2 1)
            (lam := Term.const 1) (domR := domRC2) hdom
          rwa [hρ] at hsem)
      simpa [modeC2] using this
  · refine ⟨[(2, modeC2 2, edgeC2 2 2)], ?_, ?_, ?_, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl
      exact ⟨GrC2_modeAt 2 (by norm_num), edgeC2_mem 2 2 (by simp [GrC2])⟩
    · simp
    · intro s hs
      simp only [List.head?_cons, Option.some_inj] at hs
      rw [← hs]
    · have := hbody [] (by intro Q hQ; exact absurd hQ (List.not_mem_nil))
      simpa [modeC2] using this

/-! ## The left automaton, from the file -/

/-- Declared successors of each left mode, as indices (the runner's own resolution,
`Handoff.leftModeIndex`). -/
def nextC2 : List (List ℕ) :=
  (List.range 3).map (fun l => (mLC2 l).next.filterMap (Handoff.leftModeIndex rover_coupled_IR))

/-- The file's `next` lists: `Drive → [Drift, Drive]`, `Drift → [Stop, Drift]`, `Stop → [Stop]`. -/
theorem nextC2_eq : nextC2 = [[1, 0], [2, 1], [2]] := by decide

/-- The left graph's transitions are exactly the ones the handoff runner checks. -/
theorem nextC2_transitions :
    ((List.range 3).flatMap (fun m' => (nextC2.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions rover_coupled_IR := by decide

noncomputable def guardsC2 : List (Formula (Var 4)) :=
  (List.range 3).map (fun l => hostGuard vsC2 4 Side.L (mLC2 l))

noncomputable def AC2 (dt : ℝ) : LeftAut 4 :=
  { windows := (List.range 3).map (fun l => windowSeg (leftBlock (fLC2 l)) domLC2 tgC2 dt 2),
    guards := guardsC2,
    next := nextC2 }

theorem AC2_numModes (dt : ℝ) : (AC2 dt).numModes = 3 := rfl

theorem AC2_window (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AC2 dt).window t = windowSeg (leftBlock (fLC2 t)) domLC2 tgC2 dt 2 := by
  interval_cases t <;> rfl

theorem AC2_guard (dt : ℝ) (t : ℕ) (ht : t < 3) :
    (AC2 dt).guard t = hostGuard vsC2 4 Side.L (mLC2 t) := by
  interval_cases t <;> rfl

theorem AC2_succ (dt : ℝ) (m' : ℕ) : (AC2 dt).succ m' = nextC2.getD m' [] := rfl

theorem hnextC2 (dt : ℝ) : ∀ m' < (AC2 dt).numModes, ∀ t ∈ (AC2 dt).succ m', t < (AC2 dt).numModes := by
  intro m' hm' t ht
  rw [AC2_numModes] at hm' ⊢
  rw [AC2_succ, nextC2_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardC2 (t : ℕ) (ht : t < 3) : (hostGuard vsC2 4 Side.L (mLC2 t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsC2 (mLC2 t) ?_
  interval_cases t <;> simp [mLC2, rover_coupled_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdC2 (dt : ℝ) : ∀ t < (AC2 dt).numModes, ((AC2 dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AC2_numModes] at ht
  rw [AC2_guard dt t ht]
  exact hguardC2 t ht

theorem hwinC2 (dt : ℝ) : ∀ t < (AC2 dt).numModes,
    Program.vars ((AC2 dt).window t) ⊆ {((Side.Aux, 1) : Var 4)} ∪ range Lv := by
  intro t ht
  rw [AC2_numModes] at ht
  rw [AC2_window dt t ht]
  exact vars_windowSegL_sub (fLC2 t) domLC2 1 dt 2 (hfLC2 t ht) hdomLC2

/-! ## Freshness of `u_L` -/

theorem hulenvC2 : ulC2 ∉ envC2.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRC2 h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem hulBkC2 : ulC2 ∉ (mvValid mvC2 GrC2.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvC2 GrC2.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hulGC2 (dt : ℝ) : ∀ t, ulC2 ∉ ((AC2 dt).guard t).fv := by
  intro t h
  by_cases ht : t < 3
  · exact aux_notin_range_Lv 2 (hgrdC2 dt t ht h)
  · have : (AC2 dt).guard t = Formula.tt := by
      unfold LeftAut.guard AC2 guardsC2
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlC2 (dt : ℝ) : ∀ t, FramesMv ((AC2 dt).window t) ulC2 := by
  intro t
  by_cases ht : t < 3
  · rw [AC2_window dt t ht]
    refine framesMv_window (leftBlock (fLC2 t)) domLC2 tgC2 dt 2 ulC2 (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC2 t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (AC2 dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AC2
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRC2 : ulC2 ∉ (rightAutomatonBody GrC2 mvC2).bv :=
  notMem_bv_rightAutomatonBody GrC2 mvC2 ulC2 (by decide) (aux_notin_range_Rv 2) httC2 hRvC2

/-! ## The handoff: nested constant offsets, in-kernel -/

theorem handoffC2 (dt : ℝ) : ∀ m' < (AC2 dt).numModes, ∀ t ∈ (AC2 dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat envC2 ω → Formula.sat ((AC2 dt).guard t) ω → Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [AC2_numModes] at hm'
  rw [AC2_succ, nextC2_eq] at ht
  have hm3 : m' < 3 := hm'
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl <;>
    · rw [sat_FRow _ (by norm_num)] at hF ⊢
      simp only [cRow] at hF ⊢
      norm_num at hF ⊢
      linarith

/-! ## The per-mode steps -/

theorem hstepMC2 (dt : ℝ) (hdt : 0 ≤ dt) : ∀ t < (AC2 dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envC2) (mvValid mvC2 GrC2.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 4)) ((AC2 dt).window t)
      (Program.star (rightAutomatonBody GrC2 mvC2))
      (Formula.and (Formula.and (FRow t) envC2) (mvValid mvC2 GrC2.modes.length))) σ := by
  intro t ht
  rw [AC2_numModes] at ht
  rw [AC2_window dt t ht]
  exact hstepMode_multiF GrC2 mvC2 (FRow t) envC2 _ (aux_notin_FRow 0 t) hmvenvC2 hfreshC2
    httC2 hltC2
    (by
      refine framesMv_window (leftBlock (fLC2 t)) domLC2 tgC2 dt 2 mvC2 (by decide) ?_
      intro h
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLC2 t) _ h
      exact aux_ne_Lv 0 i hi)
    (HmultiRow t ht dt hdt)

/-! ## The composed theorem -/

/-- **`rover_coupled`, Theorem 3 at the DECLARED mode-dependent invariant.** The left
program is the left automaton over the file's `next` lists (`Drive → Drift → Stop`, with
self-loops), the loop invariant is `⋀_m (u_L = m → row_m)` with `row_Drive = px_L ≤ px_R +
0.5`, `row_Drift = … + 1.0`, `row_Stop = … + 2.0`, plus the chain's bookkeeping. Composed
from the per-mode catch-up steps and the in-kernel handoffs. Z3-free. -/
theorem rover_coupled_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AC2 dt) ulC2)
      (rightAutomatonBody GrC2 mvC2)
      (psiK ulC2 ϕRow (AC2 dt).numModes domLC2 domRC2
        (mvValidR mvC2 GrC2.modes.length))) := by
  refine theorem3_modeKeyed (AC2 dt) ulC2 GrC2 mvC2 FRow ϕRow domLC2 domRC2
    (mvValid mvC2 GrC2.modes.length) (mvValidR mvC2 GrC2.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AC2 dt) GrC2 0 1 2 (by decide) (by decide) (hwinC2 dt) (hgrdC2 dt)
      (hnextC2 dt) httC2 hRvC2
  · exact hstep_modeKeyed (AC2 dt) ulC2 (rightAutomatonBody GrC2 mvC2) FRow envC2
      (mvValid mvC2 GrC2.modes.length) (aux_notin_FRow 2) hulenvC2 hulBkC2 (hulGC2 dt)
      (hframesUlC2 dt) hulRC2 (hnextC2 dt) (hstepMC2 dt hdt) (handoffC2 dt)
  · exact hddF_modeKeyed (AC2 dt) GrC2 0 1 2 (by decide) (by decide) ϕRow domLC2 domRC2
      (mvValidR mvC2 GrC2.modes.length) (hwinC2 dt) (hgrdC2 dt) (hnextC2 dt) httC2 hRvC2
      (fun m _ => canonInvM_varsL (gRow m) [] (fun g' hg' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl; exact hgRow m))
      (fun m _ => canonInvM_varsR (gRow m) []) hdomLC2 hdomRC2 rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvC2 GrC2.modes.length hv))

end RoverCoupledHandoff
end RelCertifier

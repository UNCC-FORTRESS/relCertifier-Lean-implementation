/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` — the DECLARED mode-dependent invariant, composed across left switches

`Rover3tierRung12Modal` carries one Theorem 3 per left mode (`…_ACCEL` at λ = 2, k = 7;
`…_COAST` at λ = 1, k = 4), each at its own declared row. With the rows as originally
declared the two could not be composed: ACCEL's row (`v[l] ≤ v[r] + 0.5 ∧ a[l] ≤ a[r] + 0.8`)
left more slack on `3v + a` than COAST's (`3v[l] + a[l] ≤ 3v[r] + 1.2`) admits, and the
tool's handoff check found `ACCEL → COAST` satisfiable (`docs/HANDOFF.md`). The repaired
file (rows only; dynamics, guards and evolve domains untouched) states ACCEL as the
velocity envelope plus the SAME lifted-M1 functional bound COAST uses:

    ACCEL = v[l] ≤ v[r] + 0.5 ∧ 3v[l] + a[l] ≤ 3v[r] + 1.2
    COAST = 3v[l] + a[l] ≤ 3v[r] + 1.2

Now `ACCEL → COAST` drops a conjunct (`FM_mono`), and `COAST → ACCEL` recovers the velocity
envelope from the left evolve floor `a[l] ≥ −0.3` (the DOMAIN-CONDITIONED handoff:
`3v_L + a_L ≤ 3v_R + 1.2` and `a_L ≥ −0.3` give `v_L ≤ v_R + 0.5`), in-kernel. The per-mode
steps are the base instance's own providers (`HmultiQA`, `HmultiQC`, unchanged — they are
atom-agnostic and re-elaborate at the new row), composed by `theorem3_modeKeyed` with
`u_L = (Aux, 2)`. Residuals: the base instance's four packs `VerdQA 0/1`, `VerdQC 0/1`.
-/
import RelCertifier.Instances.Rover3tierRung12Modal
import RelCertifier.Proofs.Encoding.ModeHandoff

namespace RelCertifier
namespace Rover3tierRung12Handoff

open DL DLCalTiming DLRel Parse Set Rover3tierRung12Modal

set_option maxHeartbeats 12800000

/-- The left mode variable — the third auxiliary (`mv = (Aux, 0)`, `tg = (Aux, 1)`). -/
abbrev ulQ : Var 3 := (Side.Aux, 2)

/-! ## The declared rows — the base instance's `(gQ, gsQ)` for ACCEL and `(gQC, gsQC)` for COAST -/

noncomputable def FRow : ℕ → Formula (Var 3)
  | 0 => FM gQ gsQ
  | _ => FM gQC gsQC

noncomputable def ϕRow : ℕ → RFormula (Var 3)
  | 0 => canonInvM gQ gsQ
  | _ => canonInvM gQC gsQC

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 3)) (ϕRow r) = FRow r := by
  cases r with
  | zero => exact encode_canonInvM gQ gsQ
  | succ r => exact encode_canonInvM gQC gsQC

/-- ACCEL's second component is COAST's row, term for term. -/
theorem atoms_accel_one : (atomsOf invQPF).getD 1 .tt = (atomsOf invQCPF).getD 0 .tt := by
  decide
theorem gAt_one_eq : gAt 1 = gAtC 0 := by
  unfold gAt gAtC; rw [atoms_accel_one]

/-! ## Evaluating the components -/

theorem eval_gQ (x : State (Var 3)) : Term.eval gQ x = x (Lv 0) - (x (Rv 0) + 1/2) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [gQ, gAt, atomsOf, invQPF, rover3tier_rung12_IR, Run.invToG, Run.lowerE, vsQ,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hq05,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem eval_gQC (x : State (Var 3)) :
    Term.eval gQC x = (3 * x (Lv 0) + x (Lv 2)) - (3 * x (Rv 0) + 6/5) := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  have hdLa : ("L_a".drop 2).copy = "a" := by decide
  simp [gQC, gAtC, atomsOf, invQCPF, rover3tier_rung12_IR, Run.invToG, Run.lowerE, vsQ,
    Run.resolveVar, Parse.dr, hdL, hdR, hdLa, List.findIdx?_cons, hq3, hq12,
    ITerm.toHost, Term.eval, AOp.interp, Lv, Rv]

theorem sat_domLQ (x : State (Var 3)) : Formula.sat domLQ x ↔
    (-(3:ℝ)/10 ≤ x (Lv 2) ∧ x (Lv 2) ≤ (19:ℝ)/20 ∧ 0 ≤ x (Lv 1) ∧ x (Lv 1) ≤ 100 ∧
      0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ (3:ℝ)/2) := by
  simp only [domLQ, hostEvolve, mLQ, rover3tier_rung12_IR, vsQ]
  simp [Run.lowerF, Run.lowerE, hqm03, hq095, hq00, hq100, hq15,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Lv]
  tauto

theorem sat_FRow_zero (x : State (Var 3)) : Formula.sat (FRow 0) x ↔
    (x (Lv 0) ≤ x (Rv 0) + 1/2 ∧ 3 * x (Lv 0) + x (Lv 2) ≤ 3 * x (Rv 0) + 6/5) := by
  show Formula.sat (FM gQ gsQ) x ↔ _
  rw [sat_FM_iff]
  simp only [gsQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    gAt_one_eq]
  rw [eval_gQ, show gAtC 0 = gQC from rfl, eval_gQC]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem sat_FRow_one (x : State (Var 3)) : Formula.sat (FRow 1) x ↔
    3 * x (Lv 0) + x (Lv 2) ≤ 3 * x (Rv 0) + 6/5 := by
  show Formula.sat (FM gQC gsQC) x ↔ _
  rw [sat_FM_iff]
  simp only [gsQC, List.mem_cons, List.not_mem_nil, or_false, forall_eq, eval_gQC]
  constructor <;> intro h <;> linarith

theorem aux_notin_FRow (a : Fin 3) (r : ℕ) : ((Side.Aux, a) : Var 3) ∉ (FRow r).fv := by
  cases r with
  | zero =>
      refine notMem_FM_fv (fun g' hg' h => ?_)
      have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
        simp only [gQ, gsQ, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _
      rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  | succ r =>
      refine notMem_FM_fv (fun g' hg' h => ?_)
      have hLR : g'.fv ⊆ range Lv ∪ range Rv := by
        simp only [gQC, gsQC, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAtC _
      rcases hLR h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])

/-! ## The left automaton, from the file -/

def nextQ : List (List ℕ) :=
  (List.range 2).map (fun l => (mLQ l).next.filterMap (Handoff.leftModeIndex rover3tier_rung12_IR))

/-- `ACCEL → [COAST, ACCEL]`, `COAST → [ACCEL, COAST]`. -/
theorem nextQ_eq : nextQ = [[1, 0], [0, 1]] := by decide

theorem nextQ_transitions :
    ((List.range 2).flatMap (fun m' => (nextQ.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions rover3tier_rung12_IR := by decide

noncomputable def guardsQ : List (Formula (Var 3)) :=
  (List.range 2).map (fun l => hostGuard vsQ 3 Side.L (mLQ l))

/-- ACCEL's window family at k = 7, COAST's at k = 4 — the base instance's `leftDataQ` /
`leftDataQC`. -/
noncomputable def AQ (dt : ℝ) : LeftAut 3 :=
  { windows := [windowSeg (leftBlock (fLQ 0)) domLQ tgQ dt 7,
                windowSeg (leftBlock (fLQ 1)) domLQ tgQ dt 4],
    guards := guardsQ,
    next := nextQ }

theorem AQ_numModes (dt : ℝ) : (AQ dt).numModes = 2 := rfl
theorem AQ_window_zero (dt : ℝ) : (AQ dt).window 0 = windowSeg (leftBlock (fLQ 0)) domLQ tgQ dt 7 := rfl
theorem AQ_window_one (dt : ℝ) : (AQ dt).window 1 = windowSeg (leftBlock (fLQ 1)) domLQ tgQ dt 4 := rfl
theorem AQ_guard (dt : ℝ) (t : ℕ) (ht : t < 2) :
    (AQ dt).guard t = hostGuard vsQ 3 Side.L (mLQ t) := by
  interval_cases t <;> rfl
theorem AQ_succ (dt : ℝ) (m' : ℕ) : (AQ dt).succ m' = nextQ.getD m' [] := rfl

theorem hnextQ (dt : ℝ) : ∀ m' < (AQ dt).numModes, ∀ t ∈ (AQ dt).succ m', t < (AQ dt).numModes := by
  intro m' hm' t ht
  rw [AQ_numModes] at hm' ⊢
  rw [AQ_succ, nextQ_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hguardQ (t : ℕ) (ht : t < 2) : (hostGuard vsQ 3 Side.L (mLQ t)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vsQ (mLQ t) ?_
  interval_cases t <;> simp [mLQ, rover3tier_rung12_IR, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem hgrdQ (dt : ℝ) : ∀ t < (AQ dt).numModes, ((AQ dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [AQ_numModes] at ht
  rw [AQ_guard dt t ht]
  exact hguardQ t ht

theorem hwinQ (dt : ℝ) : ∀ t < (AQ dt).numModes,
    Program.vars ((AQ dt).window t) ⊆ {((Side.Aux, 1) : Var 3)} ∪ range Lv := by
  intro t ht
  rw [AQ_numModes] at ht
  interval_cases t
  · rw [AQ_window_zero]; exact vars_windowSegL_sub (fLQ 0) domLQ 1 dt 7 (hfLQ 0 (by norm_num)) hdomLQ
  · rw [AQ_window_one]; exact vars_windowSegL_sub (fLQ 1) domLQ 1 dt 4 (hfLQ 1 (by norm_num)) hdomLQ

/-! ## Freshness of `u_L` -/

theorem hulenvQ : ulQ ∉ envQ.fv := fun h => by
  rcases h with h | h
  · exact absurd (hdomLQ h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Lv, Prod.ext_iff]))
  · exact absurd (hdomRQ h) (by rintro ⟨i, hi⟩; exact absurd hi (by simp [Rv, Prod.ext_iff]))

theorem hulBkQ : ulQ ∉ (mvValid mvQ GrQ.modes.length).fv := fun h => by
  have := mvValid_fv_sub mvQ GrQ.modes.length h
  exact absurd (Set.mem_singleton_iff.mp this) (by decide)

theorem hulGQ (dt : ℝ) : ∀ t, ulQ ∉ ((AQ dt).guard t).fv := by
  intro t h
  by_cases ht : t < 2
  · exact aux_notin_range_Lv 2 (hgrdQ dt t ht h)
  · have : (AQ dt).guard t = Formula.tt := by
      unfold LeftAut.guard AQ guardsQ
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUlQ (dt : ℝ) : ∀ t, FramesMv ((AQ dt).window t) ulQ := by
  intro t
  have hwin : ∀ (l k : ℕ), FramesMv (windowSeg (leftBlock (fLQ l)) domLQ tgQ dt k) ulQ := by
    intro l k
    refine framesMv_window (leftBlock (fLQ l)) domLQ tgQ dt k ulQ (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLQ l) _ h
    exact aux_ne_Lv 2 i hi
  by_cases ht : t < 2
  · interval_cases t
    · rw [AQ_window_zero]; exact hwin 0 7
    · rw [AQ_window_one]; exact hwin 1 4
  · have : (AQ dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window AQ
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulRQ : ulQ ∉ (rightAutomatonBody GrQ mvQ).bv :=
  notMem_bv_rightAutomatonBody GrQ mvQ ulQ (by decide) (aux_notin_range_Rv 2) httQ hRvQ

/-! ## The handoff, domain-conditioned, in-kernel -/

theorem handoffQ (dt : ℝ) : ∀ m' < (AQ dt).numModes, ∀ t ∈ (AQ dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat envQ ω → Formula.sat ((AQ dt).guard t) ω →
    Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF henv _
  rw [AQ_numModes] at hm'
  rw [AQ_succ, nextQ_eq] at ht
  have hm2 : m' < 2 := hm'
  have hdomL := (sat_domLQ ω).mp henv.1
  interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl
  · -- ACCEL → COAST: drop the velocity envelope
    rw [sat_FRow_one]; rw [sat_FRow_zero] at hF; exact hF.2
  · exact hF
  · -- COAST → ACCEL: the velocity envelope from the functional and the evolve floor a_L ≥ −0.3
    rw [sat_FRow_zero]; rw [sat_FRow_one] at hF
    exact ⟨by linarith [hdomL.1], hF⟩
  · exact hF

/-! ## The per-mode steps — the base instance's providers -/

theorem hstepMQ (dt : ℝ) (hdt : 0 ≤ dt)
    (hvA0 : VerdQA 0) (hvA1 : VerdQA 1) (hvC0 : VerdQC 0) (hvC1 : VerdQC 1) :
    ∀ t < (AQ dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) envQ) (mvValid mvQ GrQ.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((AQ dt).window t)
      (Program.star (rightAutomatonBody GrQ mvQ))
      (Formula.and (Formula.and (FRow t) envQ) (mvValid mvQ GrQ.modes.length))) σ := by
  intro t ht
  rw [AQ_numModes] at ht
  have hframe : ∀ (l k : ℕ), FramesMv (windowSeg (leftBlock (fLQ l)) domLQ tgQ dt k) mvQ := by
    intro l k
    refine framesMv_window (leftBlock (fLQ l)) domLQ tgQ dt k mvQ (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fLQ l) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · rw [AQ_window_zero]
    exact hstepMode_multiF GrQ mvQ (FM gQ gsQ) envQ _ hmvFQ hmvenvQ hfreshQ httQ hltQ (hframe 0 7)
      (HmultiQA dt hdt hvA0 hvA1 _ (by simp [leftProgsQ, leftDataQ]))
  · rw [AQ_window_one]
    exact hstepMode_multiF GrQ mvQ (FM gQC gsQC) envQ _ hmvFQC hmvenvQ hfreshQ httQ hltQ (hframe 1 4)
      (HmultiQC dt hdt hvC0 hvC1 _ (by simp [leftProgsQC, leftDataQC]))

/-! ## The composed theorem -/

/-- **`rover3tier_rung12`, Theorem 3 at the DECLARED mode-dependent invariant** (repaired
rows): `u_L`-keyed, the ACCEL window family at `v[l] ≤ v[r] + 0.5 ∧ 3v[l] + a[l] ≤ 3v[r] +
1.2` and the COAST family at `3v[l] + a[l] ≤ 3v[r] + 1.2`, over the left automaton
`ACCEL ↔ COAST` (with self-loops). Residuals: the base instance's four packs. -/
theorem rover3tier_rung12_modeKeyed (dt : ℝ) (hdt : 0 ≤ dt)
    (hvA0 : VerdQA 0) (hvA1 : VerdQA 1) (hvC0 : VerdQC 0) (hvC1 : VerdQC 1) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (AQ dt) ulQ)
      (rightAutomatonBody GrQ mvQ)
      (psiK ulQ ϕRow (AQ dt).numModes domLQ domRQ
        (mvValidR mvQ GrQ.modes.length))) := by
  refine theorem3_modeKeyed (AQ dt) ulQ GrQ mvQ FRow ϕRow domLQ domRQ
    (mvValid mvQ GrQ.modes.length) (mvValidR mvQ GrQ.modes.length)
    encode_ϕRow (encode_mvValidR _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (AQ dt) GrQ 0 1 2 (by decide) (by decide) (hwinQ dt) (hgrdQ dt)
      (hnextQ dt) httQ hRvQ
  · exact hstep_modeKeyed (AQ dt) ulQ (rightAutomatonBody GrQ mvQ) FRow envQ
      (mvValid mvQ GrQ.modes.length) (aux_notin_FRow 2) hulenvQ hulBkQ (hulGQ dt)
      (hframesUlQ dt) hulRQ (hnextQ dt) (hstepMQ dt hdt hvA0 hvA1 hvC0 hvC1) (handoffQ dt)
  · exact hddF_modeKeyed (AQ dt) GrQ 0 1 2 (by decide) (by decide) ϕRow domLQ domRQ
      (mvValidR mvQ GrQ.modes.length) (hwinQ dt) (hgrdQ dt) (hnextQ dt) httQ hRvQ
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsL gQ gsQ (fun g' hg' => by
            simp only [gQ, gsQ, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl <;> exact hgAt _)
        | succ m => exact canonInvM_varsL gQC gsQC (fun g' hg' => by
            simp only [gQC, gsQC, List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl <;> exact hgAtC _))
      (fun m _ => by
        cases m with
        | zero => exact canonInvM_varsR gQ gsQ
        | succ m => exact canonInvM_varsR gQC gsQC)
      hdomLQ hdomRQ rfl
      (fun v hv => Or.inl (mvValid_fv_sub mvQ GrQ.modes.length hv))

end Rover3tierRung12Handoff
end RelCertifier

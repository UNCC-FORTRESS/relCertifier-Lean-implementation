/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_choice` through the general Theorem 3

The running example with the economy profile, as an instance of `theorem3_of_coverX`. The
windows and their covers mirror the tool's: the `Low` window at the per-pairing stretches
(`Low` 2, `MidEco` 7/2, `MidBoost` and `High` 1; common span `δ = 2/7`, budget 4), its cover
the all-successors one with the edge `Low → PumpOff` pruned (Theorem 2 here: the level stays
above 2 along the flow); the `Mid` window (budget 1) from `MidEco` by a hop into `MidBoost`
(the same guard), from `MidBoost` and `High` by the closing segment; the `High` window from
`High`. The inadmissible starts contradict the row (`inadm`). Assumption 1 is proved for the
nominal model, with the economy set point. The covers are decided by the extended checker in
the kernel (`decide`) and transported by `decideCoveredX_sound`.
-/
import RelCertifier.InstancesV2.Choice.Modal.WatertankChoice
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceWatertank

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR watertank_choice_IRc = 1 := by
  simp [epsR, watertank_choice_IRc, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-! ## The automaton with the pruned edge `Low → PumpOff` -/

/-- The declared edge, pruned iff it is `Low → PumpOff` (the tool's non-connection
certificate). -/
noncomputable def edgeWP (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t),
    pruned := decide (s = 0 ∧ t = 4) }

noncomputable def GrP : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeWP e.1 e.2) }

theorem GrP_len : GrP.modes.length = 5 := rfl

theorem GrP_modeAt (q : ℕ) (hq : q < 5) : GrP.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrP_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : GrP.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, GrP])

theorem edgesFromP {q : ℕ} {e : REdge (Var 2)} (he : e ∈ GrP.edgesFrom q) :
    ∃ t, (q, t) ∈ edgeList ∧ e = edgeWP q t := by
  have hmem : e ∈ GrP.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [GrP, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeWP] at hsrc
  subst hsrc
  exact ⟨p.2, hp, rfl⟩

theorem edge_memP (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeWP s t ∈ GrP.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeWP]⟩

theorem GrP_guards : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.guard = guardR e.tgt := by
  intro q e he
  obtain ⟨t, -, rfl⟩ := edgesFromP he
  rfl

theorem hgRP : GuardsRight GrP := by
  intro q e he
  obtain ⟨t, ht, rfl⟩ := edgesFromP he
  exact hguardR t (edgeList_tgt (q, t) ht)

theorem hltP : ∀ q, ∀ e ∈ GrP.edgesFrom q, e.tgt < GrP.modes.length := by
  intro q e he
  obtain ⟨t, ht, rfl⟩ := edgesFromP he
  exact edgeList_tgt (q, t) ht

theorem GrP_sys (q : ℕ) (m : RMode (Var 2)) (hm : GrP.modeAt q = some m) :
    m.sys = rightBlock (fR q) (Term.const 1) := by
  obtain ⟨-, rfl⟩ := GrP_modeAt_inv hm; rfl
theorem GrP_dom (q : ℕ) (m : RMode (Var 2)) (hm : GrP.modeAt q = some m) : m.dom = domR := by
  obtain ⟨-, rfl⟩ := GrP_modeAt_inv hm; rfl
theorem GrP_weight (q : ℕ) (m : RMode (Var 2)) (hm : GrP.modeAt q = some m) : m.weight = 1 := by
  obtain ⟨-, rfl⟩ := GrP_modeAt_inv hm; rfl

theorem pruned_iff {q : ℕ} {e : REdge (Var 2)} (he : e ∈ GrP.edgesFrom q)
    (hp : e.pruned = true) : q = 0 ∧ e.tgt = 4 := by
  obtain ⟨t, -, rfl⟩ := edgesFromP he
  simpa [edgeWP] using hp

/-! ## Assumption 1 for the nominal model (the economy set point) -/

theorem fieldR (q : ℕ) (hq : q < 5) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem wellFormedR : WellFormedR GrP guardR 1 := by
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := GrP_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  refine ⟨?_, ?_⟩
  · have hw := hwfB 2 q hq5 1
    rw [show lam 2 q = 1 from by simp [lam]] at hw
    exact exists_of_wellFormedFlowB (by norm_num) hw hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq5 s
    have hx0 := ((sat_domR x).mp hd).1
    have pick : ∀ t', (q, t') ∈ edgeList → t' < 5 →
        Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
        ∃ e ∈ GrP.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
      fun t' he _ hs => ⟨edgeWP q t', edge_memP q t' he, hs⟩
    have hbet := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- Low: toward 12.5 from [2, 10): ends in [2, 12.5], inside Low or MidEco
      simp only [if_true] at hgx
      norm_num [cRc] at hbet
      obtain ⟨h1, h2⟩ := hbet
      by_cases h10 : Φ t (Rv 0) < 10
      · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by rcases h1 with h1 | h1 <;> linarith, h10⟩))
      · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; exact ⟨by linarith, by rcases h2 with h2 | h2 <;> linarith⟩))
    · -- MidEco: toward 13 from [10, 17): stays in [10, 17)
      norm_num at hgx
      norm_num [cRc] at hbet
      obtain ⟨h1, h2⟩ := hbet
      exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
        (by norm_num; exact ⟨by rcases h1 with h1 | h1 <;> linarith,
          by rcases h2 with h2 | h2 <;> linarith⟩))
    · -- MidBoost: toward 17 from [10, 17): stays in [10, 17)
      norm_num at hgx
      have hup := H.linear_up (memR 2) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 2) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      exact pick 2 (by decide) (by norm_num) ((sat_guardR 2 (by norm_num) _).mpr
        (by norm_num; exact ⟨by linarith, hlt⟩))
    · -- High: x ≥ 17 is invariant
      norm_num at hgx
      have hdn := H.linear_down (memR 3) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 3 (by decide) (by norm_num) ((sat_guardR 3 (by norm_num) _).mpr
        (by norm_num; exact hdn.1))
    · -- PumpOff: frozen (k = 0)
      norm_num at hgx
      have hdn := H.linear_down (memR 4) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hdn; norm_num at hdn
      exact pick 4 (by decide) (by norm_num) ((sat_guardR 4 (by norm_num) _).mpr
        (by norm_num; linarith))

/-! ## The windows' covers -/

/-- The certified pairings per window (the tool's flags): `Low` with `Low`, `MidEco`,
`MidBoost`, `High`; `Mid` with `MidBoost`, `High`; `High` with `High`. -/
def certified (l q : ℕ) : Bool :=
  decide ((l = 0 ∧ q ≤ 3) ∨ (l = 1 ∧ (q = 2 ∨ q = 3)) ∨ (l = 2 ∧ q = 3))

def chW (l : ℕ) : ChoiceData :=
  { jointOK := certified l, repoPre := fun _ => false, repoPost := fun _ => false,
    jointS := fun _ => [], repoS := fun _ _ => [],
    hopS := fun q σ => if l = 1 ∧ σ = SrcSetting.preJ ∧ q = 1 then [[2]] else [] }

def Bw (l : ℕ) : ℕ := if l = 0 then 4 else 1
noncomputable def δw (l : ℕ) : ℝ := if l = 0 then 2/7 else 1

theorem cov_00 : decideCoveredX GrP (chW 0) 25 ⟨0, 4, SrcSetting.preJ⟩ = true := by decide
theorem cov_01 : decideCoveredX GrP (chW 0) 25 ⟨1, 4, SrcSetting.preJ⟩ = true := by decide
theorem cov_02 : decideCoveredX GrP (chW 0) 25 ⟨2, 4, SrcSetting.preJ⟩ = true := by decide
theorem cov_11 : decideCoveredX GrP (chW 1) 25 ⟨1, 1, SrcSetting.preJ⟩ = true := by decide
theorem cov_12 : decideCoveredX GrP (chW 1) 25 ⟨2, 1, SrcSetting.preJ⟩ = true := by decide
theorem cov_13 : decideCoveredX GrP (chW 1) 25 ⟨3, 1, SrcSetting.preJ⟩ = true := by decide
theorem cov_23 : decideCoveredX GrP (chW 2) 25 ⟨3, 1, SrcSetting.preJ⟩ = true := by decide

/-- The starts the row excludes with the PumpOff mode. -/
theorem inadm4 (l : ℕ) (hl : l < 3) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hgL : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ)
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR 4)) σ) : False := by
  have h1 := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
  rw [eval_g] at h1
  have hr := (sat_guardR 4 (by norm_num) σ).mp hgR
  norm_num at hr
  have hl' := (sat_guardL l hl σ).mp hgL
  interval_cases l <;> norm_num at hl' <;> first | linarith [hl'.1] | linarith [hl']

/-! ## The window data -/

noncomputable def cRs (q : ℕ) : List (CutAtomP 2) := if q < 4 then cR q else []

noncomputable def AG (l q : ℕ) : Formula (Var 2) :=
  Formula.and (FM g (gs ++ atomTerms (cL l) (cRs q))) (Formula.and domL domR)

noncomputable def cutsG (q : ℕ) : Formula (Var 2) := cutF (cRs q)

theorem cRs_fv (q : ℕ) : ∀ a ∈ cRs q, a.2.fv ⊆ range Lv ∪ range Rv := by
  intro a ha
  unfold cRs at ha
  split_ifs at ha with hq
  · interval_cases q <;>
      simp only [cR_0, cR_1, cR_2, cR_3, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      first | exact (thr_fv_R _ _).1 | exact (thr_fv_R _ _).2
  · simp at ha

theorem cL_fv (l : ℕ) (hl : l < 3) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv ∪ range Rv := by
  intro a ha
  interval_cases l <;>
    simp only [cL_0, cL_1, cL_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2

theorem AG_fv (l : ℕ) (hl : l < 3) (q : ℕ) : (AG l q).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  rcases hv with hv | hv | hv
  · by_contra hc
    refine notMem_FM_fv (fun g' hg' hx => hc ?_) hv
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact comps_fv _ List.mem_cons_self hx
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact comps_fv _ (List.mem_cons_of_mem _ hg') hx
    simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hg'
    rcases hg' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact cL_fv l hl a ha hx
    · exact cRs_fv q a ha hx
  · exact Or.inl (hdomL hv)
  · exact Or.inr (hdomR hv)

theorem hiffRs (q : ℕ) : AtomsIff (cRs q) := by
  unfold cRs
  split_ifs with hq
  · exact hiffR q hq
  · intro a ha; simp at ha

theorem cutsG_fv (q : ℕ) : (cutsG q).fv ⊆ range Rv := by
  unfold cutsG cRs
  split_ifs with hq
  · have := region_fv q (by omega)
    simpa [region, hq] using this
  · simp [cutF, Formula.fv]

/-- The right kept atoms of the entered mode follow from its guard. -/
theorem cutsR_of_guard (q : ℕ) (hq : q < 5) (y : State (Var 2))
    (hg : Formula.sat (guardR q) y) : CutSat (cRs q) y := by
  have hg' := (sat_guardR q hq y).mp hg
  unfold cRs
  split_ifs with h4
  · rw [cutSatR_val q h4]
    interval_cases q
    · simp only [if_true] at hg' ⊢; exact ⟨hg'.1, by linarith [hg'.2]⟩
    · norm_num at hg' ⊢; exact ⟨hg'.1, hg'.2.le⟩
    · norm_num at hg' ⊢; exact ⟨hg'.1, hg'.2.le⟩
    · norm_num at hg' ⊢; exact hg'
  · intro a ha; simp at ha

theorem AG_start (l : ℕ) (hl : l < 3) (q : ℕ) (σ : State (Var 2))
    (hgL : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ)
    (hσ : Formula.sat (Formula.and (FM g gs) (Formula.and domL domR)) σ)
    (hc : Formula.sat (cutsG q) σ) : Formula.sat (AG l q) σ := by
  refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffRs q) σ).mpr ⟨hO1L l hl σ hgL, (sat_cutF _ _).mp hc⟩

theorem AG_post (l : ℕ) (hl : l < 3) (q : ℕ) (y : State (Var 2)) (h : Formula.sat (AG l q) y) :
    Formula.sat (Formula.and (Formula.and (FM g gs) (Formula.and domL domR)) (cutsG q)) y := by
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp h.1
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL l hl) (hiffRs q) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

theorem AG_hand (l : ℕ) (hl : l < 3) (q : ℕ) (e : REdge (Var 2)) (he : e ∈ GrP.edgesFrom q)
    (y : State (Var 2)) (hA : Formula.sat (AG l q) y) (hleg : SwitchLegal e y) :
    Formula.sat (AG l e.tgt) y := by
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp hA.1
  obtain ⟨hLc, -⟩ := (atomTerms_iff (hiffL l hl) (hiffRs q) y).mp hat
  have hg : Formula.sat (guardR e.tgt) y := by unfold SwitchLegal at hleg; rwa [GrP_guards q e he] at hleg
  refine ⟨(sat_FM_append g gs _ y).mpr ⟨hF, ?_⟩, hA.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffRs e.tgt) y).mpr
    ⟨hLc, cutsR_of_guard e.tgt (by have := hltP q e he; rwa [GrP_len] at this) y hg⟩

/-- The certified pairings' packs. -/
def Packs : Prop := ∀ l q, certified l q = true → Verd l q

theorem AG_box (l : ℕ) (hl : l < 3) (hv : Packs) (q : ℕ) (m : RMode (Var 2))
    (hm : GrP.modeAt q = some m) (hj : (chW l).jointOK q = true) :
    ∀ σ ω, Formula.sat (AG l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const (lam l q)))
        (Formula.and domL domR)) σ ω → Formula.sat (AG l q) ω := by
  intro σ ω hσ hω
  have hq5 := (GrP_modeAt_inv hm).1
  have hq4 : q < 4 := by
    have := hj
    simp only [chW, certified, decide_eq_true_eq] at this
    omega
  have hcRs : cRs q = cR q := by simp [cRs, hq4]
  rw [AG, hcRs] at hσ ⊢
  refine ⟨?_, sem_ode_ends_in_domain hω⟩
  exact couple_box_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) (lam l q) domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq4) (stayL l q hl) (stayR l q hq4)
    (verd_core l q hl hq5 (hv l q hj)) σ ω hσ.1 hω

/-- Theorem 2 for the pruned edge: the level stays at or above 2 along any `Low` segment,
joint or right-only, so `PumpOff`'s guard `x < 2` never holds at its end. -/
theorem level_stays (l : ℕ) (hl : l < 3) (fLx : Fin 2 → Term (Var 2)) (c : ℝ) (hc : 0 ≤ c)
    (σ ω : State (Var 2)) (hA : Formula.sat (AG l 0) σ)
    (hω : Program.sem (Program.ode (jointSys fLx (fR 0) (Term.const c)) (Formula.and domL domR))
      σ ω) : 2 ≤ ω (Rv 0) := by
  obtain ⟨-, hat⟩ := (sat_FM_append g gs _ σ).mp hA.1
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL l hl) (hiffRs 0) σ).mp hat
  have h2 : 2 ≤ σ (Rv 0) := ((cutSatR_val 0 (by norm_num) σ).mp (by simpa [cRs] using hR)).1
  have hinit : Term.eval (thrGe (Rv 0) 2) σ ≤ 0 := by
    simp [thrGe, Term.eval, AOp.interp]; linarith
  have hb := boxle_thrGe_R 0 2 fLx (fR 0) c hc (Formula.and domL domR) (Formula.and domL domR)
    (fun x h => h) (fun z _ hz => by
      rw [fR0_eval 0 (by norm_num)]; simp only [kR, cRc]; norm_num; linarith) hinit ω hω
  simp [thrGe, Term.eval, AOp.interp] at hb
  linarith

theorem not_pumpoff {y : State (Var 2)} (h2 : 2 ≤ y (Rv 0)) :
    ¬ Formula.sat (guardR 4) y := by
  intro hg
  have := (sat_guardR 4 (by norm_num) y).mp hg
  norm_num at this
  linarith

theorem hop_cover (l : ℕ) (q : ℕ) (σ : SrcSetting) (S : List ℕ)
    (hS : S ∈ (chW l).hopS q σ) (y : State (Var 2))
    (hy : Formula.sat (Formula.and (AG l q) (guardR q)) y) :
    ∃ q' ∈ S, Formula.sat (guardR q') y := by
  simp only [chW] at hS
  split_ifs at hS with hc
  · simp only [List.mem_singleton] at hS
    subst hS
    obtain ⟨-, hg⟩ := hy
    rw [hc.2.2] at hg
    have h := (sat_guardR 1 (by norm_num) y).mp hg
    norm_num at h
    refine ⟨2, List.mem_singleton_self 2, ?_⟩
    unfold guardR
    exact (sat_guardR 2 (by norm_num) y).mpr (by norm_num; exact h)
  · simp at hS

theorem coverHyps (l : ℕ) (hl : l < 3) (hv : Packs) :
    CoverHyps GrP (chW l) fR domR (fL l) domL (hostGuard vs 2 Side.L (mL l)) guardR 1 (δw l)
      (lam l) (AG l) (fun _ => Formula.tt) (fun _ _ => Formula.tt)
      (fun q _ => Formula.and (AG l q) (guardR q)) where
  hδ := by unfold δw; split_ifs <;> norm_num
  hlam := lam_pos l
  hspan := fun q => by
    unfold δw lam
    by_cases h0 : l = 0
    · subst h0
      simp only [if_true]
      split_ifs <;> norm_num
    · simp only [h0, if_false]; norm_num
  hAfv := AG_fv l hl
  hAdom := fun q y h => h.2.2
  hbox := AG_box l hl hv
  hhand := AG_hand l hl
  hprune := fun q m hm e he hp σ ω hA hω => by
    obtain ⟨rfl, ht⟩ := pruned_iff he hp
    rw [GrP_guards _ e he, ht]
    exact not_pumpoff (level_stays l hl (fL l) (lam l 0) (le_of_lt (lam_pos l 0)) σ ω hA hω)
  hrepoProg := fun q m _ pre h => by cases pre <;> simp [chW] at h
  hRJ := fun _ _ _ => trivial
  hcovJ := fun q S hS => by simp [chW] at hS
  hRR := fun _ _ _ _ _ => trivial
  hcovR := fun q σ S hS => by simp [chW] at hS
  hRS := fun q σ y hA hg _ => ⟨hA, hg⟩
  hcovS := hop_cover l

/-! ## Theorem 3 -/

theorem hcov (l : ℕ) (hl : l < 3) (q : ℕ) (hq : q < 5)
    (hadm : AdmissibleStart (hostGuard vs 2 Side.L (mL l)) (FM g gs) (Formula.and domL domR)
      (guardR q) (cutsG q)) :
    CoveredX GrP (chW l) ⟨q, Bw l, SrcSetting.preJ⟩ := by
  obtain ⟨σ, hgL, hσ, hgR, -⟩ := hadm
  have hσ' : Formula.sat (Formula.and (FM g gs) env) σ := hσ
  interval_cases l <;> interval_cases q
  · exact decideCoveredX_sound _ _ _ _ cov_00
  · exact decideCoveredX_sound _ _ _ _ cov_01
  · exact decideCoveredX_sound _ _ _ _ cov_02
  · exact (inadm 0 3 (Or.inl ⟨rfl, rfl⟩) hσ' hgL hgR).elim
  · exact (inadm4 0 (by norm_num) hσ' hgL hgR).elim
  · exact (inadm 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hσ' hgL hgR).elim
  · exact decideCoveredX_sound _ _ _ _ cov_11
  · exact decideCoveredX_sound _ _ _ _ cov_12
  · exact decideCoveredX_sound _ _ _ _ cov_13
  · exact (inadm4 1 (by norm_num) hσ' hgL hgR).elim
  · exact (inadm 2 0 (Or.inr (Or.inr ⟨rfl, by norm_num⟩)) hσ' hgL hgR).elim
  · exact (inadm 2 1 (Or.inr (Or.inr ⟨rfl, by norm_num⟩)) hσ' hgL hgR).elim
  · exact (inadm 2 2 (Or.inr (Or.inr ⟨rfl, by norm_num⟩)) hσ' hgL hgR).elim
  · exact decideCoveredX_sound _ _ _ _ cov_23
  · exact (inadm4 2 (by norm_num) hσ' hgL hgR).elim

/-- **`watertank_choice` by the general Theorem 3** (`theorem3_of_coverX`): windows of at most
one left interval, the three windows' covers (`cov_*`, decided in the kernel), Assumption 1
(`wellFormedR`), the certificates (`coverHyps`: the seven verdict packs, the pruned edge by
arithmetic, the hop certificate by arithmetic). -/
theorem watertank_choice_general (dt : ℝ) (hdt : dt ≤ 1) (hv : Packs) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsOf 1 dt domL 3 (fun l => hostGuard vs 2 Side.L (mL l)) fL))
      (rightAutomatonBody GrP mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv (regionG guardR cutsG) GrP.modes.length))) := by
  refine theorem3_of_coverX GrP 0 1 (by decide) dt g gs comps_fv domL domR hdomL hdomR guardR
    cutsG GrP_guards hgRP hguardR_all cutsG_fv fR (fun q hq => hfR q (by rwa [GrP_len] at hq))
    GrP_sys GrP_dom GrP_weight hltP 3
    (fun l => hostGuard vs 2 Side.L (mL l)) fL (fun l hl => hguardL l hl) (fun l hl => hfL l hl)
    1 wellFormedR chW Bw δw lam AG (fun _ _ => Formula.tt) (fun _ _ _ => Formula.tt)
    (fun l q _ => Formula.and (AG l q) (guardR q))
    (fun l hl => coverHyps l hl hv) ?_ ?_ ?_ ?_
  · intro l hl
    unfold Bw δw
    interval_cases l <;> norm_num <;> linarith
  · intro l hl q hq hadm
    rw [GrP_len] at hq
    exact hcov l hl q hq hadm
  · intro l hl q σ hgL hσ _ hc
    exact AG_start l hl q σ hgL hσ hc
  · intro l hl q' y hA
    exact AG_post l hl q' y hA

end ChoiceWatertank
end RelCertifier

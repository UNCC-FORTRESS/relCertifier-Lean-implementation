/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints`: the pruned automaton, Assumption 1 and the window data

The search graph with the edge `BULK → FAULT` pruned (Theorem 2: the level stays at or above
15 along the flows), Assumption 1 transported from the suite's lemma (`wellFormedR`), the
kernel-decided covers (`cov_*`, `inadm`) and the window data (`AG`, `cutsG`, `AG_box`).
The Theorem-3 part (reposition progress of `BULK` from the emitted progress certificate, the
`CoverHyps` assembly and `theorem3_of_coverX`) was retired on 2026-10-21 with the clocked
right automaton: the file is fixed at `Var 2` and has no slot for the right clock; the
benchmark's Theorem 3 is the generated bridge instance `InstancesV2/Bridge/ChargerFastSetpoints.lean`.
-/
import RelCertifier.InstancesV2.WellFormed.ChargerFastSetpoints
import RelCertifier.Checker.CoverX

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastSetpoints

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-! ## The automaton with the pruned edge `BULK → FAULT` -/

noncomputable def edgeWP (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t),
    pruned := decide (s = 0 ∧ t = 3) }

noncomputable def GrP : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeWP e.1 e.2) }

theorem GrP_len : GrP.modes.length = 4 := rfl

theorem GrP_modeAt (q : ℕ) (hq : q < 4) : GrP.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrP_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : GrP.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrP] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, GrP])

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

theorem edgesFrom_Gr {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    ∃ t, (q, t) ∈ edgeList ∧ e = edgeW q t := by
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeW] at hsrc
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
  exact hguardR_all t

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
    (hp : e.pruned = true) : q = 0 ∧ e.tgt = 3 := by
  obtain ⟨t, -, rfl⟩ := edgesFromP he
  simpa [edgeWP] using hp

/-- Assumption 1, transported from the suite's lemma. -/
theorem wellFormedR : WellFormedR GrP guardR 1 := by
  have hw := charger_fast_setpoints_wellFormedR
  rw [epsR_eq] at hw
  intro q hq m hm x hg hd htt
  have hm' : Gr.modeAt q = some m := hm
  obtain ⟨hex, hcomp⟩ := hw q hq m hm' x hg hd htt
  refine ⟨hex, ?_⟩
  intro t Φ ht H
  obtain ⟨e, he, hs⟩ := hcomp t Φ ht H
  obtain ⟨t', ht', rfl⟩ := edgesFrom_Gr he
  exact ⟨edgeWP q t', edge_memP q t' ht', hs⟩

/-! ## The guards, left and `FAULT` -/

theorem sat_guardL (l : ℕ) (hl : l < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔
      (if l = 0 then 15 ≤ ν (Lv 0) ∧ ν (Lv 0) < 80
       else if l = 1 then 80 ≤ ν (Lv 0) ∧ ν (Lv 0) < 99 else 99 ≤ ν (Lv 0)) := by
  interval_cases l <;>
    simp [hostGuard, mL, charger_fast_setpoints_IRv2, Run.lowerF, Run.lowerE, hp150, hp800,
      hp990, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Lv]

/-! ## The windows' covers -/

/-- The joint-certified pairings: `ABSORB` and `FULL` in every window. -/
def certified (_l q : ℕ) : Bool := decide (q = 1 ∨ q = 2)

/-- `BULK` is a pre-joint reposition node in the `BULK` and `ABSORB` windows. -/
def chW (l : ℕ) : ChoiceData :=
  { jointOK := certified l, repoPre := fun q => decide (q = 0 ∧ l < 2),
    repoPost := fun _ => false,
    jointS := fun _ => [], repoS := fun _ _ => [], hopS := fun _ _ => [] }

theorem cov_00 : decideCoveredX GrP (chW 0) 13 ⟨0, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_01 : decideCoveredX GrP (chW 0) 13 ⟨1, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_02 : decideCoveredX GrP (chW 0) 13 ⟨2, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_10 : decideCoveredX GrP (chW 1) 13 ⟨0, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_11 : decideCoveredX GrP (chW 1) 13 ⟨1, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_12 : decideCoveredX GrP (chW 1) 13 ⟨2, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_21 : decideCoveredX GrP (chW 2) 13 ⟨1, 2, SrcSetting.preJ⟩ = true := by decide
theorem cov_22 : decideCoveredX GrP (chW 2) 13 ⟨2, 2, SrcSetting.preJ⟩ = true := by decide

/-- The inadmissible starts: `FAULT` (level below 10) from any window, `BULK` from `FULL`. -/
theorem inadm (l q : ℕ) (hbad : (l < 3 ∧ q = 3) ∨ (l = 2 ∧ q = 0))
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hgL : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ)
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR q)) σ) : False := by
  have h1 := (sat_FM_iff g gs σ).mp hσ.1 g List.mem_cons_self
  rw [eval_g] at h1
  rcases hbad with ⟨hl, rfl⟩ | ⟨rfl, rfl⟩
  · have hr := (sat_guardR3 σ).mp hgR
    have hl' := (sat_guardL l hl σ).mp hgL
    interval_cases l <;> norm_num at hl' <;> first | linarith [hl'.1] | linarith [hl']
  · have hr := (sat_guardR 0 (by norm_num) σ).mp hgR
    have hl' := (sat_guardL 2 (by norm_num) σ).mp hgL
    norm_num at hr hl'
    linarith [hr.2]

/-! ## The window data -/

noncomputable def cRs (q : ℕ) : List (CutAtomP 2) := if q < 3 then cR q else []

noncomputable def AG (l q : ℕ) : Formula (Var 2) :=
  Formula.and (FM g (gs ++ atomTerms (cL l) (cRs q))) (Formula.and domL domR)

noncomputable def cutsG (q : ℕ) : Formula (Var 2) := cutF (cRs q)

theorem cRs_fv (q : ℕ) : ∀ a ∈ cRs q, a.2.fv ⊆ range Lv ∪ range Rv := by
  intro a ha
  unfold cRs at ha
  split_ifs at ha with hq
  · interval_cases q <;>
      simp only [cR_0, cR_1, cR_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
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

theorem cutsR_of_guard (q : ℕ) (hq : q < 4) (y : State (Var 2))
    (hg : Formula.sat (guardR q) y) : CutSat (cRs q) y := by
  unfold cRs
  split_ifs with h3
  · have hg' := (sat_guardR q h3 y).mp hg
    rw [cutSatR_val q h3]
    interval_cases q
    · simp only [if_true] at hg' ⊢; exact ⟨hg'.1, by linarith [hg'.2]⟩
    · norm_num at hg' ⊢; exact ⟨hg'.1, by linarith [hg'.2]⟩
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
  have hg : Formula.sat (guardR e.tgt) y := by
    unfold SwitchLegal at hleg; rwa [GrP_guards q e he] at hleg
  refine ⟨(sat_FM_append g gs _ y).mpr ⟨hF, ?_⟩, hA.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffRs e.tgt) y).mpr
    ⟨hLc, cutsR_of_guard e.tgt (by have := hltP q e he; rwa [GrP_len] at this) y hg⟩

def Packs : Prop := ∀ l q, certified l q = true → Verd l q

theorem AG_box (l : ℕ) (hl : l < 3) (hv : Packs) (q : ℕ) (m : RMode (Var 2))
    (hm : GrP.modeAt q = some m) (hj : (chW l).jointOK q = true) :
    ∀ σ ω, Formula.sat (AG l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR))
        σ ω → Formula.sat (AG l q) ω := by
  intro σ ω hσ hω
  have hq4 := (GrP_modeAt_inv hm).1
  have hq3 : q < 3 := by
    have := hj
    simp only [chW, certified, decide_eq_true_eq] at this
    omega
  have hcRs : cRs q = cR q := by simp [cRs, hq3]
  rw [AG, hcRs] at hσ ⊢
  refine ⟨?_, sem_ode_ends_in_domain hω⟩
  have hb := couple_box_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) (lam l) domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq3) (stayL l q hl) (stayR l q hq3)
    (verd_core l q hl hq4 (hv l q hj))
  simpa [lam] using hb σ ω hσ.1 hω

/-- Theorem 2 for the pruned edge: the level stays at or above 15 along any `BULK` segment. -/
theorem level_stays (l : ℕ) (hl : l < 3) (fLx : Fin 2 → Term (Var 2)) (c : ℝ) (hc : 0 ≤ c)
    (σ ω : State (Var 2)) (hA : Formula.sat (AG l 0) σ)
    (hω : Program.sem (Program.ode (jointSys fLx (fR 0) (Term.const c)) (Formula.and domL domR))
      σ ω) : 15 ≤ ω (Rv 0) := by
  obtain ⟨-, hat⟩ := (sat_FM_append g gs _ σ).mp hA.1
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL l hl) (hiffRs 0) σ).mp hat
  have h15 : 15 ≤ σ (Rv 0) := ((cutSatR_val 0 (by norm_num) σ).mp (by simpa [cRs] using hR)).1
  have hinit : Term.eval (thrGe (Rv 0) 15) σ ≤ 0 := by
    simp [thrGe, Term.eval, AOp.interp]; linarith
  have hb := boxle_thrGe_R 0 15 fLx (fR 0) c hc (Formula.and domL domR) (Formula.and domL domR)
    (fun x h => h) (fun z _ hz => by
      rw [fR0_eval 0 (by norm_num)]; simp only [kR, cRc]; norm_num; linarith) hinit ω hω
  simp [thrGe, Term.eval, AOp.interp] at hb
  linarith

theorem not_fault {y : State (Var 2)} (h15 : 15 ≤ y (Rv 0)) :
    ¬ Formula.sat (guardR 3) y := by
  intro hg
  have := (sat_guardR3 y).mp hg
  linarith

/- Theorem-3 part retired 2026-10-21 with the clocked right automaton (the file was fixed at
`Var 2`, no slot for the right clock); the benchmark's Theorem 3 is the generated bridge
instance `InstancesV2/Bridge/ChargerFastSetpoints.lean`.
History: git show 61d7389:RelCertifier/InstancesV2/Choice/General/ChargerFastSetpoints.lean. -/

end V2ChargerFastSetpoints
end RelCertifier

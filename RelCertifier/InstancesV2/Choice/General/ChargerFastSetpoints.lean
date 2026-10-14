/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` through the general Theorem 3, with a reposition node

The first instance whose cover uses a right-only step: in the `BULK` and `ABSORB` windows the
nominal charger may start in `BULK`, which no joint segment certifies; it repositions (charges
at the bulk rate) until `ABSORB`'s guard opens at `x = 80`, then continues with the certified
joint segments of `ABSORB` and `FULL`. The edge `BULK → FAULT` is pruned (Theorem 2: the level
stays at or above 15 along the flows). Reposition progress is discharged from the tool's
emitted **progress certificate** (`BenchProgress/charger_fast_setpoints`): its queries, rebuilt
by `progressQueriesOf` and discharged by the progress verdict runner, give the rate and
landing facts (`progressVerd_one`), which with Assumption 1 (the suite's lemma, transported),
the reposition flow certificate (`VerdD`) and the pruned edge's exclusion give `RepoProgress`
(`repoProgress_one`). The covers are decided in the kernel.
-/
import RelCertifier.InstancesV2.WellFormed.ChargerFastSetpoints
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.Progress
import RelCertifier.VerdictsV2.ProgressPin
import RelCertifier.InstancesV2.BenchProgress.charger_fast_setpoints

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2ChargerFastSetpoints

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle RelCertifier.Progress

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

/-! ## Reposition progress of `BULK`, from the emitted certificate -/

/-- The emitted certificate of `BULK` (pre-joint) in window `l`. -/
def certOf (l : ℕ) : ProgressE :=
  ⟨(mL l).name, "BULK", true, [⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩], ["ABSORB"]⟩

theorem certOf_mem (l : ℕ) (hl : l < 2) :
    certOf l ∈ charger_fast_setpoints_coverV2_progress.certs := by
  interval_cases l <;>
    simp [certOf, charger_fast_setpoints_coverV2_progress, mL, charger_fast_setpoints_IRv2]

theorem modeIdx_L (l : ℕ) (hl : l < 2) :
    modeIdx charger_fast_setpoints_IRv2.L.modes (mL l).name = l := by
  interval_cases l <;> decide
theorem modeIdx_R : modeIdx charger_fast_setpoints_IRv2.R.modes "BULK" = 0 := by decide
theorem invRow_eq (l : ℕ) (hl : l < 2) : invRowOf charger_fast_setpoints_IRv2 l = l := by
  interval_cases l <;> decide
theorem resolve_x : Run.resolveVar vs 2 Side.R "x" = some (Rv 0) := by decide
theorem mode_ABSORB : ∀ md ∈ charger_fast_setpoints_IRv2.R.modes, md.name = "ABSORB" → md = mR 1 := by
  decide

/-- The region of `BULK` (pre-joint) in window `l`, as a formula: what the anchor and the left
guard give, and what the certificate's queries assume. -/
noncomputable def regionF (l : ℕ) : Formula (Var 2) :=
  Formula.and (Formula.and (Formula.and (Formula.and domL (cutF (cL l))) (FM g gs))
    (hostGuard vs 2 Side.L (mL l))) (Formula.and domR (cutF (cR 0)))

theorem regionSat_of_regionF (l : ℕ) (hl : l < 2) (y : State (Var 2))
    (h : Formula.sat (regionF l) y) :
    RegionSat vs 2 charger_fast_setpoints_cutsV2X (mL l) (mR 0)
      (charger_fast_setpoints_IRv2.invariants.getD l ("", PForm.tt)).2 true y := by
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := h
  refine ⟨?_, (sat_cutF _ _).mp h2, ?_, fun _ => h4, ?_, (sat_cutF _ _).mp h6⟩
  · rw [domL_univ l (by omega)]; exact h1
  · intro c hc
    rw [row_eq l (by omega)] at hc
    have hcomps : hostComps vs 2 (charger_fast_setpoints_IRv2.invariants.getD 0 ("", PForm.tt)).2
        = [g] := by
      show comps = [g]
      rw [comps_eq]; simp [g, comps_eq]
    rw [hcomps, List.mem_singleton] at hc
    subst hc
    exact (sat_FM_iff g gs y).mp h3 _ List.mem_cons_self
  · rw [domR_univ 0 (by norm_num)]; exact h5

theorem AG_regionF (l : ℕ) (hl : l < 2) (y : State (Var 2)) (hA : Formula.sat (AG l 0) y)
    (hgL : Formula.sat (hostGuard vs 2 Side.L (mL l)) y) : Formula.sat (regionF l) y := by
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp hA.1
  obtain ⟨hLc, hRc⟩ := (atomTerms_iff (hiffL l (by omega)) (hiffRs 0) y).mp hat
  exact ⟨⟨⟨⟨hA.2.1, (sat_cutF _ _).mpr hLc⟩, hF⟩, hgL⟩, hA.2.2,
    (sat_cutF _ _).mpr (by simpa [cRs] using hRc)⟩

/-- An exit of the certificate is the declared, non-pruned edge `BULK → ABSORB`. -/
theorem exit_edge (y : State (Var 2))
    (h : ∃ nm ∈ ["ABSORB"], ∃ md ∈ charger_fast_setpoints_IRv2.R.modes, md.name = nm ∧
      Formula.sat (hostGuard vs 2 Side.R md) y) :
    ∃ e ∈ GrP.edgesFrom 0, e.tgt ≠ 0 ∧ e.pruned = false ∧ Formula.sat (guardR e.tgt) y := by
  obtain ⟨nm, hnm, md, hmd, hname, hs⟩ := h
  simp only [List.mem_singleton] at hnm
  subst hnm
  rw [mode_ABSORB md hmd hname] at hs
  exact ⟨edgeWP 0 1, edge_memP 0 1 (by decide), by decide, by decide, hs⟩

/-- **Reposition progress of `BULK`** in windows `BULK` and `ABSORB`, from the certificate. -/
theorem repoProgress_BULK (l : ℕ) (hl : l < 2) (hd : VerdD l 0)
    (hprog : ∀ c ∈ charger_fast_setpoints_coverV2_progress.certs,
      ProgressVerd charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X 2 c) :
    RepoProgress GrP (AG l) (hostGuard vs 2 Side.L (mL l)) (guardR 0) 0 true := by
  have hl3 : l < 3 := by omega
  -- the certificate's facts
  obtain ⟨v, hv, hrate, hline, hstart⟩ := progressVerd_one (hprog _ (certOf_mem l hl))
    ⟨"x", (80 : ℚ) / 1, true, (1 : ℚ) / 1⟩ rfl rfl
  simp only [certOf] at hv hrate hline hstart
  rw [modeIdx_L l hl, modeIdx_R, invRow_eq l hl] at hrate hline hstart
  have hv0 : v = Rv 0 := by
    have := hv
    rw [show charger_fast_setpoints_IRv2.L.stateVars = vs from rfl, resolve_x] at this
    exact (Option.some.injEq _ _).mp this.symm
  subst hv0
  have hmL : charger_fast_setpoints_IRv2.L.modes.getD l ⟨"", [], .tt, .tt, []⟩ = mL l := rfl
  have hmR : charger_fast_setpoints_IRv2.R.modes.getD 0 ⟨"", [], .tt, .tt, []⟩ = mR 0 := rfl
  have hvs : charger_fast_setpoints_IRv2.L.stateVars = vs := rfl
  simp only [hmL, hmR, hvs] at hrate hline hstart
  -- Assumption 1 at `BULK`
  have hwf0 := wellFormedR 0 (by rw [GrP_len]; norm_num) (modeW 0) (GrP_modeAt 0 (by norm_num))
  refine repoProgress_one GrP (fR 0) domL domR (hostGuard vs 2 Side.L (mL l)) guardR 0 (modeW 0)
    (GrP_modeAt 0 (by norm_num)) rfl rfl (hfR 0 (by norm_num)) hdomL hdomR (hguardL l hl3)
    hguardR_all hgRP (GrP_guards 0) (AG l) (AG_fv l hl3 0) (fun y h => ⟨h.2.1, h.2.2⟩) true 1
    one_pos (fun x hg hd' => (hwf0 x hg hd' trivial).1)
    (fun x hg hd' t Φ ht H => (hwf0 x hg hd' trivial).2 t Φ ht H) ?_ ?_ (regionF l)
    (fun y hA hgL => AG_regionF l hl y hA (hgL rfl)) 0 80 ?_ ?_ 1 one_pos ?_
  · -- the reposition flow certificate keeps the anchor
    intro σ ω hA hgL hω
    have hcRs : cRs 0 = cR 0 := by simp [cRs]
    rw [AG, hcRs] at hA ⊢
    refine ⟨?_, sem_ode_ends_in_domain hω⟩
    exact couple_box_dyn true g gs (g :: gs) (cL l) (cR 0) (fR 0) domL domR
      (hostGuard vs 2 Side.L (mL l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl3)
      (hiffR 0 (by norm_num)) (cL_fvL l hl3) (hguardL l hl3)
      (stayR_gen 0 (by norm_num) (fun _ => Term.const 0) 1 zero_le_one _)
      (verdD_core l 0 hl3 (by norm_num) hd) σ ω hA.1 hgL hω
  · -- the pruned edge is never enabled after a right-only run
    intro e he hp σ ω hA hω
    obtain ⟨-, ht⟩ := pruned_iff he hp
    rw [GrP_guards 0 e he, ht]
    exact not_fault (level_stays l hl3 (fun _ => Term.const 0) 1 zero_le_one σ ω hA hω)
  · -- landing on the line
    intro y hR hy
    exact exit_edge y (hline y (regionSat_of_regionF l hl y hR) (by simpa using hy))
  · -- landing at an already-crossed start
    intro y hR hg hy
    exact exit_edge y (hstart y (regionSat_of_regionF l hl y hR) hg (by simpa using hy))
  · -- the rate
    intro y hR hy
    have := hrate y (regionSat_of_regionF l hl y hR) (by simpa using hy)
    simpa [fR] using this

/-! ## The certificates of each window, and Theorem 3 -/

theorem coverHyps (l : ℕ) (hl : l < 3) (hv : Packs) (hd0 : VerdD 0 0) (hd1 : VerdD 1 0)
    (hprog : ∀ c ∈ charger_fast_setpoints_coverV2_progress.certs,
      ProgressVerd charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X 2 c) :
    CoverHyps GrP (chW l) fR domR (fL l) domL (hostGuard vs 2 Side.L (mL l)) guardR 1 1
      (fun _ => 1) (AG l) (fun _ => Formula.tt) (fun _ _ => Formula.tt)
      (fun q _ => Formula.and (AG l q) (guardR q)) where
  hδ := one_pos
  hlam := fun _ => one_pos
  hspan := fun _ => by norm_num
  hAfv := AG_fv l hl
  hAdom := fun q y h => h.2.2
  hbox := AG_box l hl hv
  hhand := AG_hand l hl
  hprune := fun q m hm e he hp σ ω hA hω => by
    obtain ⟨rfl, ht⟩ := pruned_iff he hp
    rw [GrP_guards _ e he, ht]
    exact not_fault (level_stays l hl (fL l) 1 zero_le_one σ ω hA hω)
  hrepoProg := fun q m hm pre hflag => by
    cases pre with
    | false => simp [chW] at hflag
    | true =>
        simp only [chW, if_true, decide_eq_true_eq] at hflag
        obtain ⟨rfl, hl2⟩ := hflag
        interval_cases l
        · exact repoProgress_BULK 0 (by norm_num) hd0 hprog
        · exact repoProgress_BULK 1 (by norm_num) hd1 hprog
  hRJ := fun _ _ _ => trivial
  hcovJ := fun q S hS => by simp [chW] at hS
  hRR := fun _ _ _ _ _ => trivial
  hcovR := fun q σ S hS => by simp [chW] at hS
  hRS := fun q σ y hA hg _ => ⟨hA, hg⟩
  hcovS := fun q σ S hS => by simp [chW] at hS

theorem hcov (l : ℕ) (hl : l < 3) (q : ℕ) (hq : q < 4)
    (hadm : AdmissibleStart (hostGuard vs 2 Side.L (mL l)) (FM g gs) (Formula.and domL domR)
      (guardR q) (cutsG q)) :
    CoveredX GrP (chW l) ⟨q, 2, SrcSetting.preJ⟩ := by
  obtain ⟨σ, hgL, hσ, hgR, -⟩ := hadm
  have hσ' : Formula.sat (Formula.and (FM g gs) env) σ := hσ
  interval_cases l <;> interval_cases q
  · exact decideCoveredX_sound _ _ _ _ cov_00
  · exact decideCoveredX_sound _ _ _ _ cov_01
  · exact decideCoveredX_sound _ _ _ _ cov_02
  · exact (inadm 0 3 (Or.inl ⟨by norm_num, rfl⟩) hσ' hgL hgR).elim
  · exact decideCoveredX_sound _ _ _ _ cov_10
  · exact decideCoveredX_sound _ _ _ _ cov_11
  · exact decideCoveredX_sound _ _ _ _ cov_12
  · exact (inadm 1 3 (Or.inl ⟨by norm_num, rfl⟩) hσ' hgL hgR).elim
  · exact (inadm 2 0 (Or.inr ⟨rfl, rfl⟩) hσ' hgL hgR).elim
  · exact decideCoveredX_sound _ _ _ _ cov_21
  · exact decideCoveredX_sound _ _ _ _ cov_22
  · exact (inadm 2 3 (Or.inl ⟨by norm_num, rfl⟩) hσ' hgL hgR).elim

/-- **`charger_fast_setpoints` by the general Theorem 3**, with the reposition node `BULK`:
windows of at most one left interval (`dt ≤ 2`), the tool's covers decided in the kernel,
Assumption 1 (the suite's lemma), the six joint packs, the two reposition packs, and the
emitted progress certificates (`hprog`: every query the progress verdict runner rebuilds is
`unsat`). -/
theorem charger_fast_setpoints_general (dt : ℝ) (hdt : dt ≤ 2) (hv : Packs)
    (hd0 : VerdD 0 0) (hd1 : VerdD 1 0)
    (hprog : ∀ c ∈ charger_fast_setpoints_coverV2_progress.certs,
      ProgressVerd charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X 2 c) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsOf 1 dt domL 3 (fun l => hostGuard vs 2 Side.L (mL l)) fL))
      (rightAutomatonBody GrP mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv (regionG guardR cutsG) GrP.modes.length))) := by
  refine theorem3_of_coverX GrP 0 1 (by decide) dt g gs comps_fv domL domR hdomL hdomR guardR
    cutsG GrP_guards hgRP hguardR_all cutsG_fv fR (fun q hq => hfR q (by rwa [GrP_len] at hq))
    GrP_sys GrP_dom GrP_weight hltP 3
    (fun l => hostGuard vs 2 Side.L (mL l)) fL (fun l hl => hguardL l hl) (fun l hl => hfL l hl)
    1 wellFormedR chW (fun _ => 2) (fun _ => 1) (fun _ _ => 1) AG (fun _ _ => Formula.tt)
    (fun _ _ _ => Formula.tt)
    (fun l q _ => Formula.and (AG l q) (guardR q))
    (fun l hl => coverHyps l hl hv hd0 hd1 hprog) (fun l _ => by simpa using hdt) ?_ ?_ ?_
  · intro l hl q hq hadm
    rw [GrP_len] at hq
    exact hcov l hl q hq hadm
  · intro l hl q σ hgL hσ _ hc
    exact AG_start l hl q σ hgL hσ hc
  · intro l hl q' y hA
    exact AG_post l hl q' y hA

end V2ChargerFastSetpoints
end RelCertifier

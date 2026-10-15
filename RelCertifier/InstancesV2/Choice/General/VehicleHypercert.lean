/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` through the general Theorem 3

The same claim as `Choice/Modal/VehicleHypercert.lean` (`v_L = v_R` over the five-mode
copy), now an instance of `theorem3_of_coverX`: the cover of every window `l` is a hop into
the left's mode from every other start, then the closing joint segment (`coverOf`); the hop's
coverage certificate is discharged here by arithmetic (the left guard and the row put the right
in the guard of `l`); Assumption 1 is proved for the nominal model (`wellFormedR`); the flow
certificates are the five verdict packs (`Verd l`). Windows are bounded by the left interval
(`dt ≤ 1`).
-/
import RelCertifier.InstancesV2.Choice.Modal.VehicleHypercert
import RelCertifier.InstancesV2.Choice.ConstMirror
import RelCertifier.Proofs.Encoding.Theorem3General
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceVehicleHypercert

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR vehicle_hypercert_IRv2 = 1 := by
  simp [epsR, vehicle_hypercert_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

/-! ## Assumption 1 for the nominal model -/

theorem edgesFrom_eq {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    ∃ t, t < 5 ∧ e = edgeW q t := by
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  have hp' := edgeList_tgt p hp
  simp only [edgeW] at hsrc
  subst hsrc
  exact ⟨p.2, hp', rfl⟩

/-- **Assumption 1 for `vehicle_hypercert`**: from every state of a mode's guard the run of one
right interval exists (the guard keeps the velocity in `[0, 0.6]` for one cycle), and every end
state is in the envelope, hence in `A0`'s guard. -/
theorem wellFormedR : WellFormedR Gr guardR 1 := by
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  refine ⟨?_, ?_⟩
  · refine odeSol_constRight (fR q) domR x 1 zero_le_one (cf q) (fR_eval q hq5) ?_
    intro t ht0 ht1 y hy
    have hy0 := hy 0
    simp only [cf, if_true] at hy0
    rw [sat_domR, hy0]
    interval_cases q <;> simp only [lo, hi, acc] at hgx ⊢ <;> constructor <;> nlinarith
  · intro t Φ _ H
    have hend : Formula.sat domR (Φ t) := H.hdom t ⟨H.hr, le_rfl⟩
    have hR := (sat_domR _).mp hend
    exact ⟨edgeW q 2, edge_mem q 2 hq5 (by norm_num),
      (sat_guardR 2 (by norm_num) _).mpr (by simp [lo, hi]; exact hR)⟩

/-! ## The cover of each window: hop into the left's mode, then the closing segment -/

/-- The window's cover data: only the diagonal pairing is certified; from any other start a
hop into `l` (pre-joint). -/
def chG (l : ℕ) : ChoiceData :=
  { jointOK := fun q => decide (q = l), repoPre := fun _ => false, repoPost := fun _ => false,
    jointS := fun _ => [], repoS := fun _ _ => [],
    hopS := fun q σ => if σ = SrcSetting.preJ ∧ q ≠ l then [[l]] else [] }

theorem coverOf (l : ℕ) (hl : l < 5) : ∀ q, q < 5 →
    CoveredX Gr (chG l) ⟨q, 1, SrcSetting.preJ⟩ := by
  intro q hq
  have hbase : CoveredX Gr (chG l) ⟨l, 1, SrcSetting.preJ⟩ :=
    CoveredX.base (modeW l) (Gr_modeAt l hl) (by simp [chG]) le_rfl
  by_cases hql : q = l
  · subst hql; exact hbase
  · refine CoveredX.hop (modeW q) (Gr_modeAt q hq) [l] (by simp [chG, hql]) (by simp) ?_ ?_
    · intro q' hq'
      simp only [List.mem_singleton] at hq'
      subst hq'
      exact mem_exitSucc_of_edge (edge_mem q q' hq hl) rfl (Ne.symm hql)
    · intro q' hq'
      simp only [List.mem_singleton] at hq'
      subst hq'
      exact hbase

/-! ## The window data -/

/-- The right kept atoms, every index (empty beyond the modes). -/
noncomputable def cRs (q : ℕ) : List (CutAtomP 2) := if q < 5 then cR q else []

/-- The anchor of pairing `(l, q)`: the row, both sides' kept atoms, the envelope. -/
noncomputable def AG (l q : ℕ) : Formula (Var 2) :=
  Formula.and (FM g (gs ++ atomTerms (cL l) (cRs q))) (Formula.and domL domR)

noncomputable def cutsG (q : ℕ) : Formula (Var 2) := cutF (cRs q)

theorem cRs_fv (q : ℕ) : ∀ a ∈ cRs q, a.2.fv ⊆ range Lv ∪ range Rv := by
  intro a ha
  unfold cRs at ha
  split_ifs at ha with hq
  · interval_cases q <;>
      simp only [cR_01 0 (by simp), cR_01 1 (by simp), cR_2, cR_34 3 (by simp),
        cR_34 4 (by simp), List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      first | exact (thr_fv_R _ _).1 | exact (thr_fv_R _ _).2
  · simp at ha

theorem cL_fv (l : ℕ) (hl : l < 5) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv ∪ range Rv := by
  intro a ha
  interval_cases l <;>
    simp only [cL_01 0 (by simp), cL_01 1 (by simp), cL_2, cL_34 3 (by simp),
      cL_34 4 (by simp), List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2

theorem AG_fv (l : ℕ) (hl : l < 5) (q : ℕ) : (AG l q).fv ⊆ range Lv ∪ range Rv := by
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

theorem cutSatRs (q : ℕ) (ν : State (Var 2)) (h0 : 0 ≤ ν (Rv 0)) (h1 : ν (Rv 0) ≤ 3/5) :
    CutSat (cRs q) ν := by
  unfold cRs
  split_ifs with hq
  · exact (cutSatR_val q hq ν).mpr (cutP_of_env q _ h0 h1)
  · intro a ha; simp at ha

theorem cutsG_fv (q : ℕ) : (cutsG q).fv ⊆ range Rv := by
  unfold cutsG cRs
  split_ifs with hq
  · exact region_fv_of (q := q) hq
  · simp [cutF, Formula.fv]
where
  region_fv_of {q : ℕ} (hq : q < 5) : (cutF (cR q)).fv ⊆ range Rv := by
    have := region_fv q
    simpa [region, hq] using this

/-- The anchor at a loop state of the window (the left guard admits the window). -/
theorem AG_start (l : ℕ) (hl : l < 5) (q : ℕ) (σ : State (Var 2))
    (hσ : Formula.sat (Formula.and (FM g gs) (Formula.and domL domR)) σ)
    (hc : Formula.sat (cutsG q) σ) : Formula.sat (AG l q) σ := by
  have hL0 := (sat_domL σ).mp hσ.2.1
  refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffRs q) σ).mpr
    ⟨(cutSatL_val l hl σ).mpr (cutP_of_env l _ hL0.1 hL0.2), (sat_cutF _ _).mp hc⟩

theorem AG_post (l : ℕ) (hl : l < 5) (q : ℕ) (y : State (Var 2)) (h : Formula.sat (AG l q) y) :
    Formula.sat (Formula.and (Formula.and (FM g gs) (Formula.and domL domR)) (cutsG q)) y := by
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp h.1
  obtain ⟨-, hR⟩ := (atomTerms_iff (hiffL l hl) (hiffRs q) y).mp hat
  exact ⟨⟨hF, h.2⟩, (sat_cutF _ _).mpr hR⟩

/-- Entry: the anchor of `q` and the entered guard give the anchor of the entered mode (every
mode's kept atoms follow from the envelope). -/
theorem AG_hand (l : ℕ) (hl : l < 5) (q : ℕ) (e : REdge (Var 2)) (_ : e ∈ Gr.edgesFrom q)
    (y : State (Var 2)) (hA : Formula.sat (AG l q) y) (_ : SwitchLegal e y) :
    Formula.sat (AG l e.tgt) y := by
  have hR0 := (sat_domR y).mp hA.2.2
  obtain ⟨hF, hat⟩ := (sat_FM_append g gs _ y).mp hA.1
  obtain ⟨hLc, -⟩ := (atomTerms_iff (hiffL l hl) (hiffRs q) y).mp hat
  refine ⟨(sat_FM_append g gs _ y).mpr ⟨hF, ?_⟩, hA.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffRs e.tgt) y).mpr ⟨hLc, cutSatRs e.tgt y hR0.1 hR0.2⟩

/-- Theorem 1 at the diagonal pairing, from its verdict pack. -/
theorem AG_box (l : ℕ) (hl : l < 5) (hv : Verd l) (q : ℕ) (m : RMode (Var 2))
    (hm : Gr.modeAt q = some m) (hj : (chG l).jointOK q = true) :
    ∀ σ ω, Formula.sat (AG l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR))
        σ ω → Formula.sat (AG l q) ω := by
  have hql : q = l := by simpa [chG] using hj
  subst hql
  intro σ ω hσ hω
  have hcRs : cRs q = cR q := by simp [cRs, hl]
  rw [AG, hcRs] at hσ ⊢
  refine ⟨?_, sem_ode_ends_in_domain hω⟩
  have hb := couple_box_cutX g gs (g :: gs) (cL q) (cR q) (fL q) (fR q) 1 domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL q hl) (hiffR q hl) (stayL q hl) (stayR q hl)
    (verd_core q hl hv)
  exact hb σ ω hσ.1 hω

/-- The hop's coverage certificate, by arithmetic: at a pre-joint start in the left guard of
`l` with `v_L = v_R`, the right is in the guard of `l`. -/
theorem hop_cover (l : ℕ) (hl : l < 5) (q : ℕ) (σ : SrcSetting) (S : List ℕ)
    (hS : S ∈ (chG l).hopS q σ) (y : State (Var 2))
    (hy : Formula.sat (Formula.and (AG l q) (Formula.and (guardR q)
      (if σ = SrcSetting.preJ then hostGuard vs 2 Side.L (mL l) else Formula.tt))) y) :
    ∃ q' ∈ S, Formula.sat (guardR q') y := by
  simp only [chG] at hS
  split_ifs at hS with hc
  · simp only [List.mem_singleton] at hS
    subst hS
    obtain ⟨hA, -, hgL⟩ := hy
    rw [if_pos hc.1] at hgL
    have heq := (sat_FMgs y).mp ((sat_FM_append g gs _ y).mp hA.1).1
    have hg := (sat_guardL l hl y).mp hgL
    refine ⟨l, List.mem_singleton_self l, ?_⟩
    unfold guardR
    rw [sat_guardR l hl, ← heq]
    exact hg
  · simp at hS

theorem edge_pruned_false {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    e.pruned = false := by
  obtain ⟨t, -, rfl⟩ := edgesFrom_eq he
  rfl

/-- The certificates of window `l`. -/
theorem coverHyps (l : ℕ) (hl : l < 5) (hv : Verd l) :
    CoverHyps Gr (chG l) fR domR (fL l) domL (hostGuard vs 2 Side.L (mL l)) guardR 1 1
      (fun _ => 1) (AG l) (fun _ => Formula.tt) (fun _ _ => Formula.tt)
      (fun q σ => Formula.and (AG l q) (Formula.and (guardR q)
        (if σ = SrcSetting.preJ then hostGuard vs 2 Side.L (mL l) else Formula.tt))) where
  hδ := one_pos
  hlam := fun _ => one_pos
  hspan := fun _ => by norm_num
  hAfv := AG_fv l hl
  hAdom := fun q y h => h.2.2
  hbox := AG_box l hl hv
  hhand := AG_hand l hl
  hprune := fun q m _ e he hp => by rw [edge_pruned_false he] at hp; cases hp
  hrepoProg := fun q m _ pre h => by cases pre <;> simp [chG] at h
  hRJ := fun _ _ _ => trivial
  hcovJ := fun q S hS => by simp [chG] at hS
  hRR := fun _ _ _ _ _ => trivial
  hcovR := fun q σ S hS => by simp [chG] at hS
  hRS := fun q σ y hA hg hgL => ⟨hA, hg, by
    split_ifs with hσ
    · exact hgL hσ
    · trivial⟩
  hcovS := hop_cover l hl

/-! ## Theorem 3 -/

theorem guardR_fv (q : ℕ) : (guardR q).fv ⊆ range Rv := hguardR_all q

theorem Gr_sys (q : ℕ) (m : RMode (Var 2)) (hm : Gr.modeAt q = some m) :
    m.sys = rightBlock (fR q) (Term.const 1) := by
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm; rfl
theorem Gr_dom (q : ℕ) (m : RMode (Var 2)) (hm : Gr.modeAt q = some m) : m.dom = domR := by
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm; rfl
theorem Gr_weight (q : ℕ) (m : RMode (Var 2)) (hm : Gr.modeAt q = some m) : m.weight = 1 := by
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm; rfl

/-- **`vehicle_hypercert` by the general Theorem 3** (`theorem3_of_coverX`): windows of at most
one left interval (`dt ≤ 1`), the five windows' covers (`coverOf`), Assumption 1
(`wellFormedR`), the certificates (`coverHyps`: the five verdict packs and the arithmetic hop
certificates). The loop invariant is the row, the envelope, and the right mode's guard with its
kept atoms. -/
theorem vehicle_hypercert_general (dt : ℝ) (hdt : dt ≤ 1) (hv : ∀ l < 5, Verd l) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsOf 1 dt domL 5 (fun l => hostGuard vs 2 Side.L (mL l)) fL))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv (regionG guardR cutsG) Gr.modes.length))) := by
  refine theorem3_of_coverX Gr 0 1 (by decide) dt g gs comps_fv domL domR hdomL hdomR guardR
    cutsG Gr_guards hgR guardR_fv cutsG_fv fR (fun q hq => hfR q (by rwa [Gr_len] at hq))
    Gr_sys Gr_dom Gr_weight hlt 5
    (fun l => hostGuard vs 2 Side.L (mL l)) fL (fun l hl => hguardL l hl) (fun l hl => hfL l hl)
    1 Formula.tt (fun _ h => by simp [Formula.fv] at h) wellFormedR chG (fun _ => 1) (fun _ => 1) (fun _ _ => 1) AG
    (fun _ _ _ _ _ => trivial) (fun _ _ => Formula.tt)
    (fun _ _ _ => Formula.tt)
    (fun l q σ => Formula.and (AG l q) (Formula.and (guardR q)
      (if σ = SrcSetting.preJ then hostGuard vs 2 Side.L (mL l) else Formula.tt)))
    (fun l hl => coverHyps l hl (hv l hl)) (fun l _ => by simpa using hdt) ?_ ?_ ?_
  · intro l hl q hq _
    rw [Gr_len] at hq
    exact coverOf l hl q hq
  · intro l hl q σ _ hσ _ hc
    exact AG_start l hl q σ hσ hc
  · intro l hl q' y hA
    exact AG_post l hl q' y hA

end ChoiceVehicleHypercert
end RelCertifier

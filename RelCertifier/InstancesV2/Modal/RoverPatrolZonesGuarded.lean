/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) over the GUARDED right automaton — Theorem 3 by a climb

`V2RoverPatrolZones.rover_patrol_zones_modeKeyed` states Theorem 3 over the `⊤`-guarded
right graph. This file states it over the GUARDED graph `GrG` (every declared edge tests the
lowered guard of the mode it enters, `GrG_guards`) at the mode-consistent region: the right
mode's guard and its kept cut atoms (`gregion`, `STALL` excluded).

The response is built from the model after the left window. Both rows bound the deployed from
above by the reference (`v_L ≤ v_R`, `s_L ≤ s_R + m`), and the reference's zone loops only
raise `v_R` (towards the zone command, which only grows along the route) and `s_R`. So the
right climbs the route: from its zone it runs to the next zone's floor and switches there
(`SLOW → MEDIUM_ECO` at `s = 20`, `MEDIUM_* → FAST` at `s = 50`, legal by the explicit end
state), then runs in `FAST` long enough that `v_R ≥ 1.2` (the deployed's highest set point; a
window never raises `v_L` above `max(v_L, 1.2)`, `windowSeg_coord_le_max`) and `s_R ≥ s_L`, and
takes the self-loop `FAST → FAST` (legal: `s ≥ 50`, `0.3 ≤ v ≤ 1.5`). No verdict pack is
needed: the theorem is Z3-free.
-/
import RelCertifier.InstancesV2.Modal.RoverPatrolZones
import RelCertifier.Proofs.Encoding.GuardedClimb
import RelCertifier.Proofs.Encoding.WindowGrowth
import RelCertifier.Proofs.Encoding.ReplayOne

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolZonesGuarded

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle V2RoverPatrolZones

/-! ## The guarded right graph -/

/-- The declared edge `s → t` tests the lowered guard of the mode it enters. -/
noncomputable def edgeG (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The file's right automaton (the modes and `next` lists of `Gr`, `edgeList_eq_IR`), every
edge guarded. -/
noncomputable def GrG : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeG e.1 e.2) }

theorem GrG_len : GrG.modes.length = 5 := rfl

theorem GrG_modeAt (q : ℕ) (hq : q < 5) : GrG.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem GrG_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : GrG.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, GrG] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, GrG])

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of the
mode it enters. -/
theorem GrG_guards : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.guard = hostGuard vs 3 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem edgeList_tgt (p : ℕ × ℕ) (hp : p ∈ edgeList) : p.2 < 5 := by
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem hltG : ∀ q, ∀ e ∈ GrG.edgesFrom q, e.tgt < GrG.modes.length := by
  intro q e he
  have hmem : e ∈ GrG.edges := List.mem_of_mem_filter he
  simp only [GrG, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact edgeList_tgt p hp

theorem hRvG : ∀ q m, GrG.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := GrG_modeAt_inv hm
  exact hRv q (modeW q) (Gr_modeAt q hq)

theorem hfreshG : ∀ q m, GrG.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRvG q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR_all (q : ℕ) : (hostGuard vs 3 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [rover_patrol_zones_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem hgRG : GuardsRight GrG := by
  intro q e he
  rw [GrG_guards q e he]
  exact hguardR_all e.tgt

theorem edgeG_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeG s t ∈ GrG.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeG]⟩

/-! ## The right guards, evaluated -/

theorem sat_guardR0 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 0)) x ↔
    (0 ≤ x (Rv 1) ∧ x (Rv 1) < 20 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR1 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR2 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) x ↔
    (20 ≤ x (Rv 1) ∧ x (Rv 1) < 50 ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 11/10) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem sat_guardR3 (x : State (Var 3)) : Formula.sat (hostGuard vs 3 Side.R (mR 3)) x ↔
    (50 ≤ x (Rv 1) ∧ 3/10 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/2) := by
  simp [hostGuard, mR, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500,
    hp03, hp06, hp09, hp11, hp15, hp02, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost,
    ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The mode-consistent region -/

/-- **The mode-consistent region** of right mode `q`: its lowered guard and its kept cut atoms
(`region`; `STALL`, the pruned sink, excluded). -/
noncomputable def gregion (q : ℕ) : Formula (Var 3) :=
  regionG (fun q => hostGuard vs 3 Side.R (mR q)) region q

theorem gregion_fv (q : ℕ) (hq : q < 5) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q hq)

theorem hmvregG : ∀ q, mv ∉ (gregion q).fv := by
  intro q
  refine notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) (hmvreg q)

/-! ## The reposition packs (the cover's `dynPre` nodes: the zones below the window's) -/

/-- The reposition pack of window `l` at right zone `q` (the left held at the window's start,
inside its guard; strata `[0, 1]`). -/
def VerdD (l q : ℕ) : Prop :=
  modalVerdDynX rover_patrol_zones_IRv2 rover_patrol_zones_cutsV2X 3 l [0, 1] true l q

theorem verdD_core (l q : ℕ) (hl : l < 4) (hq : q < 5) (h : VerdD l q) :
    VerdDynCore true (g l :: gs l) (fR q)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) (hostGuard vs 3 Side.L (mL l)) := by
  have h' := h
  unfold VerdD modalVerdDynX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## O2 for the right atoms along every flow of a driving zone (joint, or with the left
frozen): `s_R' = v_R ≥ 0`, and `v_R` contracts toward the zone's command inside the band -/

theorem stayR_gen (q : ℕ) (hq : q < 4) (fL' : Fin 3 → Term (Var 3)) (c : ℝ) (hc : 0 ≤ c)
    (D : Formula (Var 3)) (hD : ∀ z, Formula.sat D z → Formula.sat domR z) :
    AtomsStayC (cR q) (jointSys fL' (fR q) (Term.const c)) D := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hcb := cap_bounds q hq
  rw [cR_eq q hq] at ha
  simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact boxle_thrGe_R 1 _ _ _ _ hc _ D (fun x h => h)
      (fun z hz _ => by rw [fR1_eval q (by omega)]; exact ((sat_domR z).mp (hD z hz)).1) hinit
  · exact boxle_thrGe_R 0 _ _ _ _ hc _ D (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit
  · exact boxle_thrLe_R 0 _ _ _ _ hc _ D (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit

/-! ## The anchors of the cover's pairs -/

/-- The right atoms of the cover's nodes (the driving zones; `STALL` is never visited). -/
noncomputable def cR' (q : ℕ) : List (CutAtomP 3) := if q < 4 then cR q else []

noncomputable def anc (l q : ℕ) : Formula (Var 3) := FM (g l) (gs l ++ atomTerms (cL l) (cR' q))

theorem anc_eq (l q : ℕ) (hq : q < 4) :
    anc l q = FM (g l) (gs l ++ atomTerms (cL l) (cR q)) := by
  unfold anc cR'; rw [if_pos hq]

theorem anc_fv (l q : ℕ) (hl : l < 4) : (anc l q).fv ⊆ range Lv ∪ range Rv := by
  intro x hx
  by_cases hq : q < 4
  · rw [anc_eq l q hq] at hx
    by_contra hS
    exact notMem_FM_fv (fun g' hg' hxg =>
      hS (anchor_fv l q hl hq g' (by simpa using hg') hxg)) hx
  · unfold anc cR' at hx
    rw [if_neg hq] at hx
    by_contra hS
    refine notMem_FM_fv (fun g' hg' hxg => hS ?_) hx
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact comps_fv_all l _ List.mem_cons_self hxg
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact comps_fv_all l _ (List.mem_cons_of_mem _ hg') hxg
    simp only [atomTerms, List.map_append, List.mem_append, List.mem_map, List.not_mem_nil,
      false_and, exists_false, or_false] at hg'
    obtain ⟨a, ha, rfl⟩ := hg'
    exact anchor_fv l 0 hl (by norm_num) a.2 (by
      simp only [List.cons_append, List.mem_cons, List.mem_append, atomTerms, List.map_append,
        List.mem_map]
      exact Or.inr (Or.inr (Or.inl ⟨a, ha, rfl⟩))) hxg

theorem cL_fvL (l : ℕ) (hl : l < 4) : ∀ a ∈ cL l, a.2.fv ⊆ range Lv := by
  intro a ha
  rw [cL_eq l hl] at ha
  simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;>
    subst hx <;> simp [Lv]

theorem anc_box (l q : ℕ) (hl : l < 4) (hq : q < 4) (hv : Verd l q) :
    ∀ σ ω, Formula.sat (anc l q) σ →
      Program.sem (Program.ode (jointSys (fL l) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω := by
  rw [anc_eq l q hq]
  exact couple_box_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fL l) (fR q) 1 domL domR
    (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl)
    (stayR_gen q hq (fL l) 1 (by norm_num) _ (fun z hz => hz.2)) (verd_core l q hl (by omega) hv)

theorem anc_boxD (l q : ℕ) (hl : l < 4) (hq : q < 4) (hv : VerdD l q) :
    ∀ σ ω, Formula.sat (anc l q) σ → Formula.sat (hostGuard vs 3 Side.L (mL l)) σ →
      Program.sem (Program.ode (jointSys (fun _ => Term.const 0) (fR q) (Term.const 1))
        (Formula.and domL domR)) σ ω → Formula.sat (anc l q) ω := by
  rw [anc_eq l q hq]
  intro σ ω h1 h2 h3
  exact couple_box_dyn true (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fR q) domL domR
    (hostGuard vs 3 Side.L (mL l)) (fun c hc => hc) (fun c hc => hc) (hiffL l hl) (hiffR q hq)
    (cL_fvL l hl) (hguardL l hl)
    (stayR_gen q hq _ 1 (by norm_num) _ (fun z hz => by
      simp only [dynBase, if_true] at hz; exact hz.1.2))
    (verdD_core l q hl (by omega) hv) σ ω h1 (fun _ => h2) h3

/-- The right guards (driving zones), as one statement: the zone's odometer band and speed
band `[0.3, cap]`. -/
def hiS (q : ℕ) : ℝ := if q = 0 then 20 else if q < 3 then 50 else 0

theorem sat_guardRz (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) x ↔
      loL q ≤ x (Rv 1) ∧ (q < 3 → x (Rv 1) < hiS q) ∧ 3/10 ≤ x (Rv 0) ∧
        x (Rv 0) ≤ capL q := by
  interval_cases q
  · rw [sat_guardR0]; norm_num [loL, loQ, capL, capQ, hiS]
  · rw [sat_guardR1]; norm_num [loL, loQ, capL, capQ, hiS]
  · rw [sat_guardR2]; norm_num [loL, loQ, capL, capQ, hiS]
  · rw [sat_guardR3]; norm_num [loL, loQ, capL, capQ, hiS]

/-- O1 for the right: a driving zone's guard implies its kept atoms. -/
theorem hO1R (q : ℕ) (hq : q < 4) (ν : State (Var 3))
    (hg : Formula.sat (hostGuard vs 3 Side.R (mR q)) ν) : CutSat (cR q) ν := by
  have h := (sat_guardRz q hq ν).mp hg
  rw [cutSatR_val q hq ν]
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem anc_hand (l q : ℕ) (hl : l < 4) (hq : q < 4) :
    ∀ e ∈ GrG.edgesFrom q, ∀ y, Formula.sat (anc l q) y → SwitchLegal e y →
      Formula.sat (anc l e.tgt) y := by
  intro e he y hA hleg
  have hg : Formula.sat (hostGuard vs 3 Side.R (mR e.tgt)) y := by
    have := hleg; unfold SwitchLegal at this; rwa [GrG_guards q e he] at this
  rw [anc_eq l q hq] at hA
  by_cases ht : e.tgt < 4
  · rw [anc_eq l e.tgt ht]
    exact anchor_hand (hiffL l hl) (hiffR q hq) (hiffR e.tgt ht) hA (hO1R e.tgt ht y hg)
  · unfold anc cR'
    rw [if_neg ht]
    exact anchor_hand (cR' := []) (hiffL l hl) (hiffR q hq) (fun a ha => by simp at ha) hA
      (fun a ha => by simp at ha)

theorem anc_iff (l q : ℕ) (hl : l < 4) (hq : q < 4) (x : State (Var 3)) :
    Formula.sat (anc l q) x ↔
      Formula.sat (FM (g l) (gs l)) x ∧ CutSat (cL l) x ∧ CutSat (cR q) x := by
  rw [anc_eq l q hq, sat_FM_append, atomTerms_iff (hiffL l hl) (hiffR q hq)]

theorem FM_fv (l : ℕ) : (FM (g l) (gs l)).fv ⊆ range Lv ∪ range Rv := by
  intro v hv
  by_contra hn
  exact notMem_FM_fv (fun c hc hvc => hn (comps_fv_all l c hc hvc)) hv

/-! ## The right's moves: the route `SLOW → MEDIUM_* → FAST` at the odometer floors (the
explicit zone solutions give only the runs' existence; the crossing instants by the
intermediate value theorem) -/

/-- A right state of a driving zone: in its guard and the envelope. -/
def Pre (q : ℕ) (x : State (Var 3)) : Prop :=
  q < 4 ∧ Formula.sat (hostGuard vs 3 Side.R (mR q)) x ∧ Formula.sat domR x

theorem pre_R (q : ℕ) (x y : State (Var 3)) (hxy : ∀ i, x (Rv i) = y (Rv i))
    (h : Pre q x) : Pre q y := by
  obtain ⟨hq, hg, hd⟩ := h
  refine ⟨hq, ?_, ?_⟩
  · refine (Formula.coincidence _ (fun v hv => ?_)).mp hg
    obtain ⟨i, rfl⟩ := hguardR_all q hv
    exact hxy i
  · refine (Formula.coincidence domR (fun v hv => ?_)).mp hd
    obtain ⟨i, rfl⟩ := hdomR hv
    exact hxy i

theorem run_sol (q : ℕ) (hq : q < 4) (ρ : State (Var 3)) (hd : Formula.sat domR ρ)
    (τ : ℝ) (hτ : 0 ≤ τ) : ODESol (modeW q).sys (modeW q).dom ρ τ (solR (capL q) ρ) := by
  obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q hq ρ hd τ
  exact ⟨hτ, h0, hder, hmask, hdom⟩

/-- Along a zone's run from inside its speed band: the speed stays in `[v₀, cap]`, the
odometer only grows. -/
theorem run_bounds (q : ℕ) (hq : q < 4) (ρ : State (Var 3)) (hv0 : 3/10 ≤ ρ (Rv 0))
    (hvc : ρ (Rv 0) ≤ capL q) {t : ℝ} (ht : 0 ≤ t) :
    ρ (Rv 0) ≤ solR (capL q) ρ t (Rv 0) ∧ solR (capL q) ρ t (Rv 0) ≤ capL q ∧
      ρ (Rv 1) ≤ solR (capL q) ρ t (Rv 1) := by
  have he0 := ex_pos t
  have he1 := ex_le_one ht
  have he2 := ex_ge t
  rw [solR_0, solR_1]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **The odometer crosses `h`** within a stretch whose end is past it. -/
theorem run_cross (q : ℕ) (ρ : State (Var 3)) (h T : ℝ) (hT : 0 ≤ T)
    (h0 : ρ (Rv 1) ≤ h) (hT' : h ≤ solR (capL q) ρ T (Rv 1)) :
    ∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ solR (capL q) ρ τ (Rv 1) = h := by
  have hcont : ContinuousOn (fun t => solR (capL q) ρ t (Rv 1)) (Icc 0 T) := by
    have : (fun t => solR (capL q) ρ t (Rv 1)) =
        fun t => ρ (Rv 1) + capL q * t + (ρ (Rv 0) - capL q) * (1 - Real.exp (-t)) := by
      funext t; rw [solR_1]; rfl
    rw [this]
    exact Continuous.continuousOn (by fun_prop)
  have hz : solR (capL q) ρ 0 (Rv 1) = ρ (Rv 1) := by rw [solR_1, ex_zero]; ring
  obtain ⟨τ, hτI, hτ⟩ := intermediate_value_Icc hT hcont ⟨by rw [hz]; exact h0, hT'⟩
  exact ⟨τ, hτI.1, hτI.2, hτ⟩

/-- The switch ranks: `SLOW` 0, `MEDIUM_*` 1, `FAST` 2. -/
def rk (q : ℕ) : ℕ := if q = 0 then 0 else if q < 3 then 1 else 2

/-- **One climbing zone** `q → tgt` (`q < 3`): the run either stays below the zone's odometer
ceiling for the whole stretch (the self-loop is legal at its end) or crosses it within the
stretch, where `tgt`'s guard holds. -/
theorem climbZ (q tgt : ℕ) (hq : q < 3) (htgt : tgt < 4)
    (hb' : ∀ y : State (Var 3), y (Rv 1) = hiS q → 3/10 ≤ y (Rv 0) → y (Rv 0) ≤ capL q →
      Formula.sat (hostGuard vs 3 Side.R (mR tgt)) y)
    (hstay : (q, q) ∈ edgeList) (hup : (q, tgt) ∈ edgeList)
    (J : ℕ → Prop) (hJt : J tgt) (hrk : rk q < rk tgt)
    (E : ℕ → State (Var 3) → Prop) (hE : ∀ x, Pre q x → E q x)
    (ρ : State (Var 3)) (hpre : Pre q ρ) (T : ℝ) (hT : 0 ≤ T) :
    (∃ Φ, ODESol (modeW q).sys (modeW q).dom ρ T Φ ∧
      ∃ e ∈ GrG.edgesFrom q, SwitchLegal e (Φ T) ∧ E e.tgt (Φ T)) ∨
    (∃ τ, 0 ≤ τ ∧ τ ≤ T ∧ ∃ Φ, ODESol (modeW q).sys (modeW q).dom ρ τ Φ ∧
      ∃ e ∈ GrG.edgesFrom q, SwitchLegal e (Φ τ) ∧ J e.tgt ∧ rk q < rk e.tgt ∧
        Pre e.tgt (Φ τ)) := by
  obtain ⟨-, hg, hd⟩ := hpre
  have hg' := (sat_guardRz q (by omega) ρ).mp hg
  have hhi := hg'.2.1 hq
  by_cases hin : solR (capL q) ρ T (Rv 1) < hiS q
  · have hbT := run_bounds q (by omega) ρ hg'.2.2.1 hg'.2.2.2 hT
    have hgT : Formula.sat (hostGuard vs 3 Side.R (mR q)) (solR (capL q) ρ T) :=
      (sat_guardRz q (by omega) _).mpr ⟨by linarith [hg'.1], fun _ => hin,
        by linarith [hg'.2.2.1], hbT.2.1⟩
    exact Or.inl ⟨solR (capL q) ρ, run_sol q (by omega) ρ hd T hT, edgeG q q,
      edgeG_mem q q hstay, hgT,
      hE _ ⟨by omega, hgT, solR_stays q (by omega) ρ hd hT⟩⟩
  · push Not at hin
    obtain ⟨τ, hτ0, hτT, hτ⟩ := run_cross q ρ (hiS q) T hT hhi.le hin
    have hbτ := run_bounds q (by omega) ρ hg'.2.2.1 hg'.2.2.2 hτ0
    have hgt := hb' _ hτ (by linarith [hg'.2.2.1]) hbτ.2.1
    exact Or.inr ⟨τ, hτ0, hτT, solR (capL q) ρ, run_sol q (by omega) ρ hd τ hτ0, edgeG q tgt,
      edgeG_mem q tgt hup, hgt, hJt, hrk, ⟨htgt, hgt, solR_stays q (by omega) ρ hd hτ0⟩⟩

theorem enter1 (y : State (Var 3)) (hs : y (Rv 1) = hiS 0) (h3 : 3/10 ≤ y (Rv 0))
    (hc : y (Rv 0) ≤ capL 0) : Formula.sat (hostGuard vs 3 Side.R (mR 1)) y := by
  rw [sat_guardR1]
  simp only [hiS, if_true] at hs
  have : capL 0 = 3/5 := by norm_num [capL, capQ]
  refine ⟨by rw [hs], by rw [hs]; norm_num, h3, by linarith⟩
theorem enter2 (y : State (Var 3)) (hs : y (Rv 1) = hiS 0) (h3 : 3/10 ≤ y (Rv 0))
    (hc : y (Rv 0) ≤ capL 0) : Formula.sat (hostGuard vs 3 Side.R (mR 2)) y := by
  rw [sat_guardR2]
  simp only [hiS, if_true] at hs
  have : capL 0 = 3/5 := by norm_num [capL, capQ]
  refine ⟨by rw [hs], by rw [hs]; norm_num, h3, by linarith⟩
theorem enter3 (q : ℕ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (y : State (Var 3)) (hs : y (Rv 1) = hiS q)
    (h3 : 3/10 ≤ y (Rv 0)) (hc : y (Rv 0) ≤ capL q) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) y := by
  rw [sat_guardR3]
  have hh : hiS q = 50 := by
    simp only [hiS, show q ≠ 0 by omega, if_false, show q < 3 by omega, if_true]
  have : capL q ≤ 3/2 := (cap_bounds q (by omega)).2
  exact ⟨by rw [hs, hh], h3, by linarith⟩

/-- The cover's joint nodes and reposition nodes per window: `SLOW` window every zone joint;
`MEDIUM_ECO` window `SLOW` a reposition node; `MEDIUM_BRISK` window `SLOW` and `MEDIUM_ECO`
reposition nodes; `FAST` window `MEDIUM_*` reposition nodes (its `SLOW` start is
inadmissible). -/
def J (l q : ℕ) : Prop := q < 4 ∧ (l = 0 ∨ (l = 1 ∧ 1 ≤ q) ∨ (l = 2 ∧ 2 ≤ q) ∨ (3 ≤ l ∧ q = 3))
def D (l q : ℕ) : Prop := (l = 1 ∧ q = 0) ∨ (l = 2 ∧ q < 2) ∨ (l = 3 ∧ 1 ≤ q ∧ q < 3)

theorem hmove (l : ℕ) (E : ℕ → State (Var 3) → Prop) (hE : ∀ q x, Pre q x → E q x) :
    HMove GrG modeW (J l) rk Pre E := by
  intro q hJ ρ hpre T hT
  have hq4 : q < 4 := hJ.1
  interval_cases q
  · exact climbZ 0 1 (by norm_num) (by norm_num) enter1 (by decide) (by decide) (J l)
      ⟨by norm_num, by
        rcases hJ.2 with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · omega
        · omega
        · omega⟩ (by decide) E (fun x hx => hE 0 x hx) ρ hpre T hT
  · exact climbZ 1 3 (by norm_num) (by norm_num) (enter3 1 le_rfl (by norm_num)) (by decide)
      (by decide) (J l) ⟨by norm_num, by
        rcases hJ.2 with h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
        · omega
        · omega⟩ (by decide) E (fun x hx => hE 1 x hx) ρ hpre T hT
  · exact climbZ 2 3 (by norm_num) (by norm_num) (enter3 2 (by norm_num) le_rfl) (by decide)
      (by decide) (J l) ⟨by norm_num, by
        rcases hJ.2 with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h, by norm_num⟩))
        · omega⟩ (by decide) E (fun x hx => hE 2 x hx) ρ hpre T hT
  · -- `FAST`: the odometer has no ceiling; the self-loop is legal at the end
    obtain ⟨-, hg, hd⟩ := hpre
    have hg' := (sat_guardRz 3 (by norm_num) ρ).mp hg
    have hbT := run_bounds 3 (by norm_num) ρ hg'.2.2.1 hg'.2.2.2 hT
    have hgT : Formula.sat (hostGuard vs 3 Side.R (mR 3)) (solR (capL 3) ρ T) :=
      (sat_guardRz 3 (by norm_num) _).mpr ⟨by linarith [hg'.1], fun h => absurd h (by norm_num),
        by linarith [hg'.2.2.1], hbT.2.1⟩
    exact Or.inl ⟨solR (capL 3) ρ, run_sol 3 (by norm_num) ρ hd T hT, edgeG 3 3,
      edgeG_mem 3 3 (by decide), hgT,
      hE 3 _ ⟨by norm_num, hgT, solR_stays 3 (by norm_num) ρ hd hT⟩⟩

/-- The reposition ranks: `SLOW` 2, `MEDIUM_*` 1, `FAST` 0. -/
def rkD (q : ℕ) : ℕ := if q = 0 then 2 else if q < 3 then 1 else 0

/-- **One reposition** `q → tgt` (the left frozen): the zone alone climbs to its odometer
ceiling and switches into `tgt`, a joint node of the window. -/
theorem repoZ (q tgt : ℕ) (hq : q < 3) (htgt : tgt < 4)
    (hb' : ∀ y : State (Var 3), y (Rv 1) = hiS q → 3/10 ≤ y (Rv 0) → y (Rv 0) ≤ capL q →
      Formula.sat (hostGuard vs 3 Side.R (mR tgt)) y)
    (hup : (q, tgt) ∈ edgeList) (hne : tgt ≠ q) (hrk : rkD tgt < rkD q)
    (J : ℕ → Prop) (hJt : J tgt) (D : ℕ → Prop) (ρ : State (Var 3)) (hpre : Pre q ρ) :
    ∃ τ Φ, ODESol (modeW q).sys (modeW q).dom ρ τ Φ ∧
      ∃ e ∈ GrG.edgesFrom q, SwitchLegal e (Φ τ) ∧ e.tgt ≠ q ∧ rkD e.tgt < rkD q ∧
        ((J e.tgt ∧ Pre e.tgt (Φ τ)) ∨ (D e.tgt ∧ ¬ J e.tgt ∧ Pre e.tgt (Φ τ))) := by
  obtain ⟨-, hg, hd⟩ := hpre
  have hg' := (sat_guardRz q (by omega) ρ).mp hg
  have hhi := hg'.2.1 hq
  -- the odometer grows at least `0.3` per unit time: past the ceiling by `T₀`
  set T₀ := (hiS q - ρ (Rv 1)) / (3/10) with hT₀
  have hT₀0 : 0 ≤ T₀ := div_nonneg (by linarith) (by norm_num)
  have hpast : hiS q ≤ solR (capL q) ρ T₀ (Rv 1) := by
    have he := ex_ge T₀
    have hc := cap_bounds q (by omega)
    rw [solR_1]
    have h1 : ρ (Rv 1) + ρ (Rv 0) * T₀ ≤
        ρ (Rv 1) + capL q * T₀ + (ρ (Rv 0) - capL q) * (1 - ex T₀) := by
      have : 0 ≤ (capL q - ρ (Rv 0)) * (T₀ - 1 + ex T₀) :=
        mul_nonneg (by linarith [hg'.2.2.2]) (by linarith)
      nlinarith
    have h2 : (3/10) * T₀ ≤ ρ (Rv 0) * T₀ := mul_le_mul_of_nonneg_right hg'.2.2.1 hT₀0
    have h3 : (3/10) * T₀ = hiS q - ρ (Rv 1) := by rw [hT₀]; field_simp
    linarith
  obtain ⟨τ, hτ0, -, hτ⟩ := run_cross q ρ (hiS q) T₀ hT₀0 hhi.le hpast
  have hbτ := run_bounds q (by omega) ρ hg'.2.2.1 hg'.2.2.2 hτ0
  have hgt := hb' _ hτ (by linarith [hg'.2.2.1]) hbτ.2.1
  exact ⟨τ, solR (capL q) ρ, run_sol q (by omega) ρ hd τ hτ0, edgeG q tgt, edgeG_mem q tgt hup,
    hgt, hne, hrk, Or.inl ⟨hJt, ⟨htgt, hgt, solR_stays q (by omega) ρ hd hτ0⟩⟩⟩

theorem hexit (l : ℕ) : HExit GrG modeW (J l) (D l) rkD Pre Pre := by
  intro q hD hnJ ρ hpre
  have hq3 : q < 3 := by rcases hD with ⟨-, rfl⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ <;> omega
  interval_cases q
  · -- `SLOW` (a reposition node of the `MEDIUM_*` windows): to 20, into the window's zone
    rcases hD with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h, -⟩
    · exact repoZ 0 1 (by norm_num) (by norm_num) enter1 (by decide) (by decide) (by decide)
        (J 1) ⟨by norm_num, Or.inr (Or.inl ⟨rfl, le_rfl⟩)⟩ (D 1) ρ hpre
    · exact repoZ 0 2 (by norm_num) (by norm_num) enter2 (by decide) (by decide) (by decide)
        (J 2) ⟨by norm_num, Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl⟩))⟩ (D 2) ρ hpre
    · omega
  · exact repoZ 1 3 (by norm_num) (by norm_num) (enter3 1 le_rfl (by norm_num)) (by decide)
      (by decide) (by decide) (J l) ⟨by norm_num, by
        rcases hD with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h, by norm_num⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))⟩ (D l) ρ hpre
  · exact repoZ 2 3 (by norm_num) (by norm_num) (enter3 2 (by norm_num) le_rfl) (by decide)
      (by decide) (by decide) (J l) ⟨by norm_num, by
        rcases hD with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h, by norm_num⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))⟩ (D l) ρ hpre

/-! ## The response to one gated window: the cover's derivation, replayed -/

theorem respondR (l : ℕ) (hl : l < 4) (dt : ℝ) (hJv : ∀ q, J l q → Verd l q)
    (hDv : ∀ q, D l q → VerdD l q) (q : ℕ) (hq : q < 4) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hg : Formula.sat (hostGuard vs 3 Side.R (mR q)) σ) :
    GResp GrG q (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt (0 + 1))
      (fun qf => Formula.and (Formula.and (FM (g l) (gs l)) env) (region qf)) σ := by
  have hJD : ∀ q, J l q ∨ D l q → q < 4 := by
    intro q h; rcases h with h | h
    · exact h.1
    · rcases h with ⟨-, rfl⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ <;> omega
  refine replay_gresp_k GrG modeW fR domR (fL l) domL (hostGuard vs 3 Side.L (mL l)) 1
    hgRG (hfL l hl) hdomL hdomR (hguardL l hl) 1 one_pos (J l) (D l)
    (fun q h => hfR q (by have := hJD q h; omega)) rk rkD 3
    (fun q _ => by unfold rk; split_ifs <;> norm_num)
    (fun q h => GrG_modeAt q (by have := hJD q h; omega)) (fun _ _ => rfl) (fun _ _ => rfl)
    (anc l) (fun q => anc_fv l q hl)
    (fun q h => anc_box l q hl h.1 (hJv q h))
    (fun q h => anc_boxD l q hl (hJD q (Or.inr h)) (hDv q h))
    (fun q h => anc_hand l q hl (hJD q h))
    Pre Pre Pre pre_R pre_R
    (hmove l _ (fun _ _ h => h)) (hexit l) dt 0 (fun h => absurd h (lt_irrefl 0)) q σ ?_
    hσ.2.1 _ ?_
  · intro hgL
    have hpre : Pre q σ := ⟨hq, hg, hσ.2.2⟩
    have hA : Formula.sat (anc l q) σ :=
      (anc_iff l q hl hq σ).mpr ⟨hσ.1, hO1L l hl σ hgL, hO1R q hq σ hg⟩
    refine ⟨?_, hA⟩
    by_cases hJq : J l q
    · exact Or.inl ⟨hJq, hpre⟩
    · by_cases hDq : D l q
      · exact Or.inr ⟨hDq, hJq, hpre⟩
      · -- the only remaining start, the `FAST` window from `SLOW`, is inadmissible:
        -- `s_L ≥ 50`, `s_R < 20`, `s_L ≤ s_R + 2`
        exfalso
        have hl3 : l = 3 := by
          by_contra h
          interval_cases l <;> interval_cases q <;> simp_all [J, D]
        subst hl3
        have hq0 : q = 0 := by
          by_contra h
          interval_cases q <;> simp_all [J, D]
        subst hq0
        have hL := (cutSatL_val 3 (by norm_num) σ).mp (hO1L 3 (by norm_num) σ hgL)
        have hR := (sat_guardRz 0 (by norm_num) σ).mp hg
        have hrow := (sat_FRow 3 (by norm_num) σ).mp hσ.1
        have h20 := hR.2.1 (by norm_num)
        norm_num [loL, loQ, hiS, mL', mQ] at hL h20 hrow
        linarith [hL.1, hrow.2]
  · intro ν hwin q' μ hμL hpre hA
    have hdomLν : Formula.sat domL ν :=
      windowSeg_end_domL (leftBlock (fL l)) domL tg dt (0 + 1) (by norm_num) hwin
    obtain ⟨hq', hgq, hdR⟩ := hpre
    have hA' := (anc_iff l q' hl hq' _).mp hA
    have hF : Formula.sat (FM (g l) (gs l)) μ := by
      refine (sat_of_agree (FM_fv l) (fun i => ?_) (fun i => ?_)).mp hA'.1
      · rw [mergeLR_L, hμL i]
      · rw [mergeLR_R]
    refine ⟨⟨hF, ?_, hdR⟩, (sat_region_lt q' hq' μ).mpr (hO1R q' hq' μ hgq)⟩
    refine (Formula.coincidence domL (fun v hv => ?_)).mpr hdomLν
    obtain ⟨i, rfl⟩ := hdomL hv
    exact hμL i

/-! ## The per-mode steps and Theorem 3 -/

theorem hulRG : uL ∉ (rightAutomatonBody GrG mv).bv :=
  notMem_bv_rightAutomatonBody_G GrG mv uL (by decide) (aux_notin_range_Rv 2) hgRG hRvG

theorem hulBkG : uL ∉ (mvRegion mv gregion GrG.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv gregion GrG.modes.length (fun q hq => gregion_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hstepMG (dt : ℝ) (hJv : ∀ l < 4, ∀ q, J l q → Verd l q)
    (hDv : ∀ l < 4, ∀ q, D l q → VerdD l q) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv gregion GrG.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((A dt).window t)
      (Program.star (rightAutomatonBody GrG mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv gregion GrG.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  refine hstepMode_GR GrG mv (FRow t) env gregion _ (aux_notin_FRow 0 t) hmvenv hmvregG
    hfreshG (guardsFresh_of_right GrG 0 hgRG) hltG (framesGw t dt 0 (by decide)) ?_
  refine HMode_regionG GrG mv _ region GrG_guards (FRow t) env _ ?_ ?_
  · intro q _ σ ν hrun
    exact frames_right (vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht)
      hdomL) (hguardR_all q) hrun
  · intro q hq σ _ hσ hg hreg
    rw [GrG_len] at hq
    by_cases h4 : q < 4
    · exact respondR t ht dt (hJv t ht) (hDv t ht) q h4 hσ hg
    · exact absurd hreg (not_sat_region_sink q h4 σ)

/-- **`rover_patrol_zones` (suite_v2), Theorem 3 over the GUARDED right automaton, at the
mode-consistent region, by replaying the emitted cover**
(`InstancesV2/BenchCovers/rover_patrol_zones.lean`, λ = 1). The statement of
`rover_patrol_zones_modeKeyed` (the declared rows keyed by `u_L`, the file's left automaton,
the envelope) with every right edge testing the entered mode's guard (`GrG_guards`) and the
loop invariant's right region the current mode's guard and kept cut atoms (`mvRegionR` at
`gregion`; `STALL` excluded). Response: the right keeps time with the window in the joint
zones, climbing the route `SLOW → MEDIUM_ECO → FAST` (`MEDIUM_BRISK → FAST`) at the odometer
floors, every stretch preserved by its joint pack `Verd l q`; a start in a zone below the
window's (a reposition node) first repositions the right alone up the route under the
reposition pack `VerdD l q`; the `FAST` window's `SLOW` start is contradictory
(inadmissible). Every switch is legal against the entered zone's guard; the explicit zone
solutions give only the runs' existence (the crossing instants by the intermediate value
theorem). -/
theorem rover_patrol_zones_guarded (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) (d10 : VerdD 1 0) (d20 : VerdD 2 0) (d21 : VerdD 2 1)
    (d31 : VerdD 3 1) (d32 : VerdD 3 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody GrG mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv gregion GrG.modes.length))) := by
  have hJv : ∀ l < 4, ∀ q, J l q → Verd l q := by
    intro l hl q hJ
    obtain ⟨hq, hlq⟩ := hJ
    match l, q, hl, hq with
    | 0, 0, _, _ => exact h00
    | 0, 1, _, _ => exact h01
    | 0, 2, _, _ => exact h02
    | 0, 3, _, _ => exact h03
    | 1, 1, _, _ => exact h11
    | 1, 2, _, _ => exact h12
    | 1, 3, _, _ => exact h13
    | 2, 2, _, _ => exact h22
    | 2, 3, _, _ => exact h23
    | 3, 3, _, _ => exact h33
    | 1, 0, _, _ => exfalso; omega
    | 2, 0, _, _ => exfalso; omega
    | 2, 1, _, _ => exfalso; omega
    | 3, 0, _, _ => exfalso; omega
    | 3, 1, _, _ => exfalso; omega
    | 3, 2, _, _ => exfalso; omega
  have hDv : ∀ l < 4, ∀ q, D l q → VerdD l q := by
    intro l _ q hD
    rcases hD with ⟨rfl, rfl⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq1, hq3⟩
    · exact d10
    · interval_cases q
      · exact d20
      · exact d21
    · interval_cases q
      · exact d31
      · exact d32
  refine theorem3_modeKeyed (A dt) uL GrG mv FRow ϕRow domL domR
    (mvRegion mv gregion GrG.modes.length) (mvRegionR mv gregion GrG.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) hgRG hRvG
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody GrG mv) FRow env
      (mvRegion mv gregion GrG.modes.length) (aux_notin_FRow 2) hulenv hulBkG (hulG dt)
      (hframesUl dt) hulRG (hnext dt) (hstepMG dt hJv hDv) (handoff dt)
  · exact hddF_modeKeyed_G (A dt) GrG 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv gregion GrG.modes.length) (hwin dt) (hgrd dt) (hnext dt) hgRG hRvG
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv gregion GrG.modes.length (fun q hq => gregion_fv q hq) hv)

end V2RoverPatrolZonesGuarded
end RelCertifier

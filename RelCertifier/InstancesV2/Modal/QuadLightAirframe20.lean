/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20` (suite_v2) — modal Theorem 3

Quadratic-drag climb dynamics on both sides; one left window (`CLIMB`), right `CLIMB` plus
the pruned sink `LIMIT`. Existence is discharged Z3-free by the strict-face viability route
(both evolve faces of the stretched right field are strict).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.Proofs.Flow.StratifiedFaces
import RelCertifier.InstancesV2.Cuts.quad_light_airframe_20

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2QuadLightAirframe20

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["w"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := quad_light_airframe_20_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := quad_light_airframe_20_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

/-- The declared invariant's components (`invComponents` of the row). -/
noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (quad_light_airframe_20_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := [comps.getD 1 (Term.const 0)]

/-- The kept cut atoms (extended certificate) of left mode `l` / right mode `q`. -/
noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX quad_light_airframe_20_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX quad_light_airframe_20_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp745 : Run.parseRat "7.45" = some ((149:ℚ)/20) := by
  have h : parseQ "7.45" = some (⟨745, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp125 : Run.parseRat "1.25" = some ((5:ℚ)/4) := by
  have h : parseQ "1.25" = some (⟨125, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp40 : Run.parseRat "4.0" = some (4 : ℚ) := by
  have h : parseQ "4.0" = some (⟨40, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp35 : Run.parseRat "3.5" = some ((7:ℚ)/2) := by
  have h : parseQ "3.5" = some (⟨35, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp25 : Run.parseRat "2.5" = some ((5:ℚ)/2) := by
  have h : parseQ "2.5" = some (⟨25, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp26 : Run.parseRat "2.6" = some ((13:ℚ)/5) := by
  have h : parseQ "2.6" = some (⟨26, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

/-- Left field: `w' = 149/20 − 5/4·w²`. -/
theorem fL0_eval (l : ℕ) (hl : l < 1) (x : State (Var 2)) :
    Term.eval (fL l 0) x = 149/20 - 5/4 * (x (Lv 0) * x (Lv 0)) := by
  interval_cases l
  simp [fL, hostDyn, mL, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp745,
    hp125, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]

theorem fL1_eval (l : ℕ) (hl : l < 1) (x : State (Var 2)) :
    Term.eval (fL l 1) x = 0 := by
  interval_cases l
  simp [fL, hostDyn, mL, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp745,
    hp125, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]

/-- Right climb field: `w' = c_q − w²` (`CLIMB`: `c = 4`). -/
noncomputable def cRc (_q : ℕ) : ℝ := 4

theorem cRc_pos (q : ℕ) (hq : q < 1) : 0 < cRc q := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]
theorem cRc_lt (q : ℕ) (hq : q < 1) : cRc q < 49/4 := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]
theorem cRc_le (q : ℕ) (hq : q < 1) : cRc q ≤ 4 := by
  obtain rfl : q = 0 := by omega
  norm_num [cRc]

theorem fR0_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fR q 0) x = cRc q - x (Rv 0) * x (Rv 0) := by
  interval_cases q
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp40,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q
  simp [fR, hostDyn, mR, quad_light_airframe_20_IRv2, vs, Run.dynOf, Run.lowerE, hp40,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 7/2) := by
  simp only [domL, hostEvolve, mL, quad_light_airframe_20_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp35, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2) := by
  simp only [domR, hostEvolve, mR, quad_light_airframe_20_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp35, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 1) : hostEvolve vs 2 Side.L (mL l) = domL := by
  obtain rfl : l = 0 := by omega
  rfl
theorem domR_univ (q : ℕ) (hq : q < 2) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 1)),
     Term.binop .sub (Term.var (Rv 0))
       (Term.binop .add (Term.var (Lv 0)) (Term.const (((1:ℚ)/2 : ℚ) : ℝ)))] := by
  have hdL : ("L_w".drop 2).copy = "w" := by decide
  have hdR : ("R_w".drop 2).copy = "w" := by decide
  simp [comps, hostComps, quad_light_airframe_20_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp10, hp05, ITerm.toHost, Lv, Rv]

theorem eval_g (x : State (Var 2)) : Term.eval g x = x (Lv 0) - (x (Rv 0) + 1) := by
  simp [g, comps_eq, Term.eval, AOp.interp]
theorem eval_gs0 (x : State (Var 2)) :
    Term.eval (gs.getD 0 (Term.const 0)) x = x (Rv 0) - (x (Lv 0) + 1/2) := by
  simp [gs, comps_eq, Term.eval, AOp.interp]

/-! ## The cut families, concretely -/

theorem gL_thr0 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "w") (.num "0.0")) = thrGe (Lv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_thr1 : hostAtomG vs 2 Side.L (.cmp "<=" (.var "w") (.num "2.5"))
    = thrLe (Lv 0) (5/2) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp25, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gR_thr0 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "w") (.num "0.0")) = thrGe (Rv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_thr1 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "w") (.num "2.6"))
    = thrLe (Rv 0) (13/5) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp26, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "w") (.num "0.0")), thrGe (Lv 0) 0),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "w") (.num "2.5")), thrLe (Lv 0) (5/2))] := by
  rw [← gL_thr0, ← gL_thr1]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "w") (.num "0.0")), thrGe (Rv 0) 0),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "w") (.num "2.6")), thrLe (Rv 0) (13/5))] := by
  rw [← gR_thr0, ← gR_thr1]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 1) :
    ∀ x ∈ cutAtomsOfX quad_light_airframe_20_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l
  intro x hx
  simp [cutAtomsOfX, quad_light_airframe_20_cutsV2X, mL, quad_light_airframe_20_IRv2] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 1) :
    ∀ x ∈ cutAtomsOfX quad_light_airframe_20_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q
  intro x hx
  simp [cutAtomsOfX, quad_light_airframe_20_cutsV2X, mR, quad_light_airframe_20_IRv2] at hx
  rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 1) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 1) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 1) :
    ∀ ν, Formula.sat (hostGuard vs 2 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard quad_light_airframe_20_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l; rfl
  · interval_cases l
    intro x hx
    simp [cutAtomsOfX, quad_light_airframe_20_cutsV2X, mL, quad_light_airframe_20_IRv2] at hx
    rcases hx with rfl | rfl <;> simp
  · interval_cases l
    intro x hx
    simp [cutAtomsOfX, quad_light_airframe_20_cutsV2X, mL, quad_light_airframe_20_IRv2] at hx
    rcases hx with rfl | rfl <;>
      simp [Run.lowerF, Run.lowerE, hp00, hp25, vs, Run.resolveVar, List.findIdx?_cons]
  · interval_cases l
    simp [mL, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp00, hp25, vs,
      Run.resolveVar, List.findIdx?_cons]

/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 2) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 2 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 2) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 2 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 2 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 2 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 1) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by
      obtain rfl : l = 0 := by omega
      simp [mL, quad_light_airframe_20_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 2) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, quad_light_airframe_20_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, quad_light_airframe_20_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, quad_light_airframe_20_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 1) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by
      obtain rfl : l = 0 := by omega
      simp [mL, quad_light_airframe_20_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · intro x hx
    simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp

theorem thr_fv_L (j : Fin 2) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 2) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 1) (hq : q < 1) :
    ∀ c ∈ g :: gs ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  obtain rfl : l = 0 := by omega
  obtain rfl : q = 0 := by omega
  simp only [cL_0, cR_0, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases ha with rfl | rfl <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 |
      exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (CLIMB 0, LIMIT 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range quad_light_airframe_20_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (quad_light_airframe_20_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 2 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [edgeW, Gr]

theorem hRv : ∀ q m, Gr.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR q) (Term.const 1) (hfR q hq) (by simp [Term.fv]) hy
  · exact hdomR hy

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

theorem hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem hguardR (q : ℕ) (hq : q < 2) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;> simp [mR, quad_light_airframe_20_IRv2, Parse.PForm.namesFree,
      Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 2 := by decide

theorem hgR : GuardsRight Gr := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact hguardR p.2 (edgeList_tgt p hp)

/-- **The graph is the guarded automaton**: every declared edge tests the lowered guard of
the mode it enters. -/
theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 2 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

/-- A non-sink right mode's region implies its own (lowered) guard. -/
theorem guard_of_region (q : ℕ) (hq : q < 1) (μ : State (Var 2)) (h : CutSat (cR q) μ) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) μ := by
  have hv : ∀ a ∈ cR q, Term.eval a.2 μ ≤ 0 := fun a ha => (hiffR q hq a ha μ).mp (h a ha)
  interval_cases q <;>
  · rw [cR_0] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      thrGe, thrLe, Term.eval, AOp.interp] at hv
    simp [hostGuard, mR, quad_light_airframe_20_IRv2, Run.lowerF, Run.lowerE, hp00, hp26, vs, Run.resolveVar,
      List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval,
      Rv]
    constructor <;> linarith [hv.1, hv.2]

/-! ## Regions: the right mode's kept cut atoms; the pruned sink is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 2) :=
  if q < 1 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 1) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region1 (ν : State (Var 2)) : ¬ Formula.sat (region 1) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (hq : q < 2) : (region q).fv ⊆ range Rv := by
  by_cases h1 : q < 1
  · simp only [region, h1, if_true]
    intro x hx
    unfold cutF at hx
    have key : ∀ (L : List (CutAtomP 2)) (acc : Formula (Var 2)),
        acc.fv ⊆ range Rv → (∀ a ∈ L, a.1.fv ⊆ range Rv) →
        (L.foldl (fun d a => Formula.and d a.1) acc).fv ⊆ range Rv := by
      intro L
      induction L with
      | nil => intro acc hacc _; simpa using hacc
      | cons a L ih =>
          intro acc hacc hL
          simp only [List.foldl_cons]
          refine ih _ ?_ (fun b hb => hL b (List.mem_cons_of_mem _ hb))
          intro y hy
          rcases hy with hy | hy
          · exact hacc hy
          · exact hL a List.mem_cons_self hy
    refine key (cR q) Formula.tt (by simp [Formula.fv]) ?_ hx
    intro a ha y hy
    interval_cases q
    simp only [cR_0, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h1, if_false]
    simp [Formula.fv, Term.fv]

/-! ## The stretch of the left window (the emitted cover's λ) -/

noncomputable def lam (_l : ℕ) : ℝ := 7/4

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; norm_num

/-! ## O2: the kept atoms stay along the joint flows (field sign on the evolve band) -/

theorem sat_D (z : State (Var 2)) (hz : Formula.sat (Formula.and domL domR) z) :
    (0 ≤ z (Lv 0) ∧ z (Lv 0) ≤ 7/2) ∧ (0 ≤ z (Rv 0) ∧ z (Rv 0) ≤ 7/2) :=
  ⟨(sat_domL z).mp hz.1, (sat_domR z).mp hz.2⟩

theorem stayL (l q : ℕ) (hl : l < 1) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hf := fL0_eval l hl
  interval_cases l
  rw [cL_0] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z hD hz => by
        rw [hf]; have := (sat_D z hD).1; nlinarith) hinit
  · exact boxle_thrLe_L 0 (5/2) _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z hD hz => by
        rw [hf]; have := (sat_D z hD).1; nlinarith) hinit

theorem stayR (l q : ℕ) (hq : q < 1) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q hq
  have hc := le_of_lt (lam_pos l)
  interval_cases q
  rw [cR_0] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z hD hz => by
        rw [hf]; have := (sat_D z hD).2; simp only [cRc]; nlinarith) hinit
  · exact boxle_thrLe_R 0 (13/5) _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z hD hz => by
        rw [hf]; have := (sat_D z hD).2; simp only [cRc]; nlinarith) hinit

/-! ## Existence: both evolve faces strict for the stretched drag field (Z3-free) -/

/-- The faces (`w_R ∈ [0, 7/2]`): `−w_R` and `w_R − 7/2`. -/
noncomputable def faceLo : Term (Var 2) :=
  Term.binop AOp.sub (Term.const 0) (Term.var (Rv 0))
noncomputable def faceHi : Term (Var 2) :=
  Term.binop AOp.sub (Term.var (Rv 0)) (Term.const ((7:ℝ)/2))

theorem faces_fv : ∀ gT ∈ [faceLo, faceHi], ∀ x ∈ gT.fv, x ∈ range Rv := by
  intro gT hgT x hx
  rcases List.mem_cons.mp hgT with rfl | hgT
  · simp only [faceLo, Term.fv, Set.mem_union, Set.mem_empty_iff_false, false_or,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩
  · rw [List.mem_singleton] at hgT
    subst hgT
    simp only [faceHi, Term.fv, Set.mem_union, Set.mem_empty_iff_false, or_false,
      Set.mem_singleton_iff] at hx
    exact ⟨0, hx.symm⟩

theorem faces_val (x : State (Var 2)) (h : ∀ gT ∈ [faceLo, faceHi], Term.eval gT x ≤ 0) :
    0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 7/2 := by
  have h0 := h faceLo List.mem_cons_self
  have h1 := h faceHi (by simp)
  simp only [faceLo, faceHi, Term.eval, AOp.interp] at h0 h1
  constructor <;> linarith

/-- The frozen-left joint system at right mode `q`, stretched by `λ`: the `w_R` row is
`λ (c_q − w_R²)`, every other row is zero. -/
theorem odeField_R (l q : ℕ) (hq : q < 1) (x : State (Var 2)) :
    odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x
      = fun c => if c = Rv 0 then lam l * (cRc q - x (Rv 0) * x (Rv 0)) else 0 := by
  funext c
  by_cases hc : c ∈ (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))).bound
  · rw [show odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x c
        = ((jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))).rhs c).eval x from by
      simp only [odeField, if_pos hc]]
    obtain ⟨p, hp, hfst⟩ : ∃ p ∈ jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)),
        p.1 = c := by simpa [ODESystem.bound, List.mem_map] using hc
    rw [← hfst, ODESystem.rhs_eq_of_mem (jointSys_wellFormed _ _ _) hp]
    rw [jointSys_split] at hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      have : (Lv j : Var 2) ≠ Rv 0 := by simp [Lv, Rv, Prod.ext_iff]
      simp [Term.eval, this]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      fin_cases j
      · simp [Term.eval, AOp.interp, fR0_eval q hq]
      · have : (Rv (1 : Fin 2) : Var 2) ≠ Rv 0 := by simp [Rv, Prod.ext_iff]
        simp [Term.eval, AOp.interp, fR1_eval q hq, this]
  · have hcR : c ≠ Rv 0 := by
      intro hceq
      refine hc ?_
      rw [hceq, jointSys_split]
      simp only [ODESystem.bound, List.map_append, List.mem_append]
      exact Or.inr (by
        simp only [rightBlock, List.map_map, List.mem_map]
        exact ⟨0, List.mem_finRange 0, rfl⟩)
    simp only [odeField, if_neg hc, if_neg hcR]

/-- Strict inflow on the lower face (`w_R = 0` ⟹ `Lie = −λ c_q < 0`). -/
theorem hbndS_lo (l q : ℕ) (hq : q < 1) (x : State (Var 2))
    (hface : Term.eval faceLo x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceLo ω) x < 0 := by
  have hx0 : x (Rv 0) = 0 := by
    simp only [faceLo, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceLo ω)
      = fun y => (-1 : ℝ) * y (Rv 0) + 0 := by
    funext y
    simp [faceLo, Term.eval, AOp.interp]
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) (-1) 0 x,
    odeField_R l q hq]
  simp only [if_pos rfl, if_true, hx0]
  have h1 := lam_pos l
  have h2 := cRc_pos q hq
  nlinarith

/-- Strict inflow on the upper face (`w_R = 7/2` ⟹ `Lie = λ (c_q − 49/4) < 0`). -/
theorem hbndS_hi (l q : ℕ) (hq : q < 1) (x : State (Var 2))
    (hface : Term.eval faceHi x = 0) :
    Lie (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l)))
      (fun ω => Term.eval faceHi ω) x < 0 := by
  have hx0 : x (Rv 0) = 7/2 := by
    simp only [faceHi, Term.eval, AOp.interp] at hface
    linarith
  have hfun : (fun ω : State (Var 2) => Term.eval faceHi ω)
      = fun y => (1 : ℝ) * y (Rv 0) + (-(7/2)) := by
    funext y
    simp [faceHi, Term.eval, AOp.interp]
    ring
  rw [hfun, lie_affine_coord _ (jointSys_wellFormed _ _ _) (Rv 0) 1 (-(7/2)) x,
    odeField_R l q hq]
  simp only [if_pos rfl, if_true, hx0]
  have h1 := lam_pos l
  have h2 := cRc_lt q hq
  nlinarith

/-- Hand Lipschitz bound: on unit balls around face-region anchors (`|w_R| ≤ 9/2`), the
field is `16`-Lipschitz (`λ · 9 = 63/4`). -/
theorem hLip (l q : ℕ) (hq : q < 1) (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    LipschitzOnWith 16 (odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))))
      (Metric.closedBall ν 1) := by
  obtain ⟨hν0, hν1⟩ := faces_val ν hν
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [odeField_R l q hq, odeField_R l q hq]
  rw [Metric.mem_closedBall] at hx hy
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hx
  have hyc : |y (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have h := dist_le_pi_dist y ν (Rv 0)
    rw [Real.dist_eq] at h
    exact le_trans h hy
  have hνb : |ν (Rv 0)| ≤ 7/2 := abs_le.mpr ⟨by linarith, hν1⟩
  have hxb : |x (Rv 0)| ≤ 9/2 := by
    have h2 := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    linarith
  have hyb : |y (Rv 0)| ≤ 9/2 := by
    have h2 := abs_sub_abs_le_abs_sub (y (Rv 0)) (ν (Rv 0))
    linarith
  refine dist_pi_le_iff (by positivity) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_true]
    rw [Real.dist_eq]
    have hdiff : lam l * (cRc q - x (Rv 0) * x (Rv 0))
        - lam l * (cRc q - y (Rv 0) * y (Rv 0))
        = -(lam l) * (x (Rv 0) + y (Rv 0)) * (x (Rv 0) - y (Rv 0)) := by ring
    rw [hdiff, abs_mul, abs_mul]
    have h2 : |x (Rv 0) + y (Rv 0)| ≤ 9 := by
      calc |x (Rv 0) + y (Rv 0)| ≤ |x (Rv 0)| + |y (Rv 0)| := abs_add_le _ _
        _ ≤ 9 := by linarith
    have h3 : |x (Rv 0) - y (Rv 0)| ≤ dist x y := by
      have h := dist_le_pi_dist x y (Rv 0)
      rwa [Real.dist_eq] at h
    have hd : (0:ℝ) ≤ dist x y := dist_nonneg
    have habs : |(-(lam l) : ℝ)| = 7/4 := by simp only [lam]; norm_num
    have hstep : |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (7/4) * 9 * dist x y := by
      rw [habs]
      have hnn : (0:ℝ) ≤ |x (Rv 0) - y (Rv 0)| := abs_nonneg _
      nlinarith [abs_nonneg (x (Rv 0) + y (Rv 0))]
    have hcoe : ((16 : NNReal) : ℝ) = 16 := by norm_num
    calc |(-(lam l) : ℝ)| * |x (Rv 0) + y (Rv 0)| * |x (Rv 0) - y (Rv 0)|
        ≤ (7/4) * 9 * dist x y := hstep
      _ ≤ ((16 : NNReal) : ℝ) * dist x y := by rw [hcoe]; nlinarith
  · simp only [if_neg hc]
    simp [dist_nonneg]

/-- Hand field bound: `‖field‖ ≤ 43` on the same balls (`λ (c_q + 81/4) ≤ 7/4 · 97/4`). -/
theorem hfbnd (l q : ℕ) (hq : q < 1) (ν : State (Var 2))
    (hν : ∀ gT ∈ [faceLo, faceHi], Term.eval gT ν ≤ 0) :
    ∀ x ∈ Metric.closedBall ν 1,
      ‖odeField (jointSys (fun _ => Term.const 0) (fR q) (Term.const (lam l))) x‖
        ≤ (43:NNReal) := by
  intro x hx
  obtain ⟨hν0, hν1⟩ := faces_val ν hν
  rw [Metric.mem_closedBall] at hx
  have hxc : |x (Rv 0) - ν (Rv 0)| ≤ 1 := by
    have := dist_le_pi_dist x ν (Rv 0)
    rw [Real.dist_eq] at this
    linarith
  have hxb : |x (Rv 0)| ≤ 9/2 := by
    have := abs_sub_abs_le_abs_sub (x (Rv 0)) (ν (Rv 0))
    have hνb : |ν (Rv 0)| ≤ 7/2 := abs_le.mpr ⟨by linarith, hν1⟩
    linarith [abs_le.mp hνb]
  rw [odeField_R l q hq]
  refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr ?_
  intro c
  by_cases hc : c = Rv 0
  · subst hc
    simp only [if_pos rfl, Real.norm_eq_abs]
    have hsq : x (Rv 0) * x (Rv 0) ≤ (9/2) * (9/2) := by
      have := abs_le.mp hxb
      nlinarith
    have hsq0 : 0 ≤ x (Rv 0) * x (Rv 0) := mul_self_nonneg _
    have hc0 := cRc_pos q hq
    have hc4 := cRc_le q hq
    have hl : lam l = 7/4 := rfl
    rw [abs_le, hl]
    push_cast
    refine ⟨by nlinarith [hsq, hsq0], by nlinarith [hsq, hsq0]⟩
  · simp only [if_neg hc]
    norm_num

/-- **The existence residual, discharged Z3-free**: both faces of the evolve band are strict
for the stretched quadratic-drag field; hand analytic data (`K = 16`, `L = 43`, unit balls).
For `dt < 0` the segment property is vacuous. -/
theorem es (l q : ℕ) (hq : q < 1) (dt : ℝ) (A : Formula (Var 2)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const (lam l)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  rcases lt_or_ge dt 0 with hneg | hdt
  · intro s _ hs0 hsdt
    exact absurd (lt_of_le_of_lt (le_trans hs0 hsdt) hneg) (lt_irrefl 0)
  have hR := (sat_domR σ).mp hσ.2.2
  have hupd : Function.update σ tg 0 (Rv 0) = σ (Rv 0) :=
    Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  refine HExistSegB_of_viability_stratified (fL l) (fR q) (Term.const (lam l))
    domL domR [faceLo, faceHi] [] [] 0 le_rfl
    (jointSys_wellFormed _ _ _)
    (by
      intro gT hgT x hx hb
      obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL l) _ hb
      obtain ⟨j, hj⟩ := faces_fv gT (by simpa using hgT) x hx
      rw [← hj] at hi
      exact absurd hi (by simp [Lv, Rv, Prod.ext_iff]))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by
      intro gT hgT x _ hface
      rcases List.mem_cons.mp hgT with rfl | hgT
      · exact hbndS_lo l q hq x hface
      · rw [List.mem_singleton] at hgT
        subst hgT
        exact hbndS_hi l q hq x hface)
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro i hi; exact absurd hi (by simp))
    (by
      intro x hS _
      rw [sat_domR]
      exact faces_val x (fun gT hgT => hS gT (by simpa using hgT)))
    16 43 1 one_pos
    (fun ν0 h0 => hLip l q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    (fun ν0 h0 => hfbnd l q hq ν0 (fun gT hgT => h0 gT (by simpa using hgT)))
    dt hdt
    (Function.update σ tg 0)
    (by
      intro gT hgT
      rcases List.mem_cons.mp hgT with rfl | hgT
      · simp only [faceLo, Term.eval, AOp.interp]
        rw [hupd]; linarith [hR.1]
      · rw [List.mem_singleton] at hgT
        subst hgT
        simp only [faceHi, Term.eval, AOp.interp]
        rw [hupd]; linarith [hR.2])
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))
    (by intro gT hgT; exact absurd hgT (List.not_mem_nil))

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l`, right mode `q`, at the cover's λ and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX quad_light_airframe_20_IRv2 quad_light_airframe_20_cutsV2X 2 0 [0, 1] (lam l) l q

theorem verd_core (l q : ℕ) (hl : l < 1) (hq : q < 2) (h : Verd l q) :
    VerdXCore (g :: gs) (fL l) (fR q) (lam l)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 1) (hq : q < 1) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX g gs (g :: gs) (cL l) (cR q) (fL l) (fR q) (lam l) (lam_pos l) domL domR 1 dt
    (hfL l hl) (hfR q (by omega)) hdomL hdomR (anchor_fv l q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl (by omega) hv) (es l q hq dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 2)} {A B : Formula (Var 2)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 2)}
    (h : Formula.sat (faModal (Equiv.refl (Var 2)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 1) (hqs : qs < 1) (dt : ℝ) (hv : Verd l qs)
    (path : List ℕ) (hpath : ∀ p ∈ path, p < 2) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq ((path.map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR))
        ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region qs))) σ := by
  have htgF : tg ∉ (FM g (gs ++ atomTerms (cL l) (cR qs))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l qs hl hqs g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM g (gs ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2)))
    (by
      intro h hh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact ⟨hfR p (hpath p hp), by simp [Term.fv], hdomR⟩)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh σ' hσ' _
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      obtain ⟨ρ, hsem, hρσ⟩ := static_hop_existsR (fR := fR p)
        (lam := Term.const 1) (domR := domR) hσ'.2.2
      exact ⟨ρ, hsem, hρσ ▸ hσ'⟩)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR qs) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 2)
        (hfR qs (by omega)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  rw [show (path.map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = path.map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from by rw [List.map_map]; rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs hqs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt qs hqs ν).mpr hRν⟩

/-! ## The step provider: stay in the certified start mode -/

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  [(hostGuard vs 2 Side.L (mL 0), fL 0, domL, 1)]

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 2)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact ⟨hguardL 0 (by norm_num), hfL 0 (by norm_num), hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 2)) (ψ : Formula (Var 2))
    {σ : State (Var 2)}
    (hbody : Formula.sat (hostGuard vs 2 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 2))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

/-- **Nonblocking at the end of a response**, discharged from the explicit end state: a
non-sink mode's region implies its own guard (`guard_of_region`), so the stay `q → q` is
enabled wherever the response ends, and the loop postcondition holds for it. -/
theorem nonblock {F' : Formula (Var 2)} (q : ℕ) (hq : q < 1) :
    NonblockingAt Gr q (Formula.and F' (region q)) (fun qf => Formula.and F' (region qf)) := by
  intro μ hμ
  refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide), ?_, hμ⟩
  exact guard_of_region q hq μ ((sat_region_lt q hq μ).mp hμ.2)

theorem stayCase (l q : ℕ) (hl : l < 1) (hq : q < 1) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ)
    (hreg : Formula.sat (region q) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR q)))
      (Formula.and domL domR)) σ := by
    refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
    exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
      ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
  exact gresp_final (Gr_modeAt q (by omega)) (respond l q hl hq dt hv [] (by simp) hanchor) (nonblock q hq)

theorem Hmulti (dt : ℝ) (h00 : Verd 0 0) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ → Formula.sat (region q) σ →
      GResp Gr q P
        (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ hreg
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  subst hP
  match q, hq, hreg with
  | 0, _, hreg => exact stayCase 0 0 (by norm_num) (by norm_num) dt h00 hσ hreg
  | 1, _, hreg => exact absurd hreg (not_sat_region1 σ)

/-! ## Theorem 3 -/

/-- **`quad_light_airframe_20` (suite_v2), modal Theorem 3 at the declared invariant.** Left:
the guard-gated `CLIMB` window (the 20 %-lighter airframe, `w' = 7.45 − 1.25 w²`, entered
inside its guard); right: the two-mode automaton of the file (`CLIMB`, `w' = 4 − w²`, and the
limiter sink `LIMIT`; declared edges, the pruned `CLIMB → LIMIT` included); the loop invariant
is the declared row `w_L ≤ w_R + 1 ∧ w_R ≤ w_L + 0.5`, the evolve envelope `[0, 3.5]` on both
sides, and the right mode's region — its kept cut atoms (`w_R ∈ [0, 2.6]` in `CLIMB`),
`LIMIT` excluded (the pruned sink: the right is never in it). The response stays in `CLIMB`
on the certified joint segment at the cover's λ = 7/4. Existence is discharged Z3-free (both
evolve faces strict for the stretched drag field). Residual: one stratified verdict pack over
the cut-narrowed domain (`modalVerdX`, the tool's own queries). -/
theorem quad_light_airframe_20_modal (dt : ℝ) (h00 : Verd 0 0) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv region Gr.modes.length))) := by
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg : ∀ q, mv ∉ (region q).fv := by
    intro q h
    by_cases hq : q < 2
    · exact aux_notin_range_Rv 0 (region_fv q hq h)
    · simp only [region, show ¬ q < 1 from by omega, if_false] at h
      simp [Formula.fv, Term.fv] at h
  refine theorem3_faithful_multiR_LR Gr mv (FM g gs) domL domR region
    (leftProgs dt) (canonInvM g gs) (encode_canonInvM g gs) ?_ ?_ ?_
  · refine sides_disjoint 0 1 0 (by decide) (by decide) ?_ ?_
    · refine vars_bigChoice_sub _ _ ?_
      intro p hp
      simp only [leftProgs, List.mem_map] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      exact vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL d hd).1
        (hL d hd).2.1 (hL d hd).2.2
    · intro x hx
      rw [Program.rename_refl] at hx
      rcases vars_bodyG_sub Gr _ hgR hRv hx with hx | hx
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)))
      · exact Or.inr hx
  · exact hstep_assembled_GR Gr mv (FM g gs) env region (leftProgs dt) hmvF hmvenv hmvreg
      hfresh (guardsFresh_of_right Gr 0 hgR) hlt (hframes dt) (Hmulti dt h00)
  · exact hddF_multiR_G Gr 0 1 dt leftData region (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q hq => region_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end V2QuadLightAirframe20
end RelCertifier

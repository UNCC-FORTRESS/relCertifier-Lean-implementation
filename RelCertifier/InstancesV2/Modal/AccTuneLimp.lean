/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp` (suite_v2) — the mode-keyed Theorem 3

The file declares one relational row per LEFT mode (`CRUISE`: `|v_L − v_R| ≤ 2`,
`LIMP`: `v_L ≤ v_R + 2 ∧ v_R ≤ v_L + 6.5`). This leaf states Theorem 3 at exactly that mode-keyed
invariant, keyed by the left mode variable `u_L = (Aux, 2)`, over the left automaton of the
file's `next` lists (`CRUISE → [CRUISE, LIMP]`, `LIMP → [LIMP]`) against the right automaton
of the file (`NORMAL`, `COMFORT`, `SPORT`, `DISENGAGE`, declared edges). Lowered at `n = 3`
(state `v` at coordinate 0, coordinates 1 and 2 are pads) so that the three auxiliaries
`mv = (Aux, 0)`, `tg = (Aux, 1)`, `u_L = (Aux, 2)` exist.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.acc_tune_limp

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccTuneLimp

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := acc_tune_limp_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := acc_tune_limp_IRv2.R.modes.getD q dm

abbrev mv : Var 3 := (Side.Aux, 0)
abbrev tg : Var 3 := (Side.Aux, 1)
abbrev uL : Var 3 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domL : Formula (Var 3) := hostEvolve vs 3 Side.L (mL 0)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
noncomputable def env : Formula (Var 3) := Formula.and domL domR

/-- The declared row of left mode `r` (`invComponents` of `invariants.getD r`). -/
noncomputable def comps (r : ℕ) : List (Term (Var 3)) :=
  hostComps vs 3 (acc_tune_limp_IRv2.invariants.getD r ("", PForm.tt)).2
noncomputable def g (r : ℕ) : Term (Var 3) := (comps r).getD 0 (Term.const 0)
noncomputable def gs (r : ℕ) : List (Term (Var 3)) := [(comps r).getD 1 (Term.const 0)]

/-- The per-left-mode host row and its relational form. -/
noncomputable def FRow (r : ℕ) : Formula (Var 3) := FM (g r) (gs r)
noncomputable def ϕRow (r : ℕ) : RFormula (Var 3) := canonInvM (g r) (gs r)

theorem encode_ϕRow (r : ℕ) : encode (Equiv.refl (Var 3)) (ϕRow r) = FRow r :=
  encode_canonInvM _ _

/-- The kept cut atoms (extended certificate) of left mode `l` / right mode `q`. -/
noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.L (cutAtomsOfX acc_tune_limp_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.R (cutAtomsOfX acc_tune_limp_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp075 : Run.parseRat "0.75" = some ((3:ℚ)/4) := by
  have h : parseQ "0.75" = some (⟨75, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp220 : Run.parseRat "22.0" = some (22 : ℚ) := by
  have h : parseQ "22.0" = some (⟨220, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp360 : Run.parseRat "36.0" = some (36 : ℚ) := by
  have h : parseQ "36.0" = some (⟨360, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp65 : Run.parseRat "6.5" = some ((13:ℚ)/2) := by
  have h : parseQ "6.5" = some (⟨65, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

/-- `CRUISE`: `v' = 0.75 (30 − v)`. -/
theorem fL0_eval_C (x : State (Var 3)) :
    Term.eval (fL 0 0) x = 3/4 * (30 - x (Lv 0)) := by
  simp [fL, hostDyn, mL, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp075, hp300,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]

/-- `LIMP`: `v' = 0.3 (25 − v)`. -/
theorem fL0_eval_L (x : State (Var 3)) :
    Term.eval (fL 1 0) x = 3/10 * (25 - x (Lv 0)) := by
  simp [fL, hostDyn, mL, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp03, hp250,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Lv]

/-- Right fields: `v' = k_q (30 − v)` (`NORMAL` 0.5, `COMFORT` 0.4, `SPORT` 0.6). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 1/2 else if q = 1 then 2/5 else 3/5

theorem kR_pos (q : ℕ) : 0 < kR q := by unfold kR; split_ifs <;> norm_num

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (30 - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp04, hp06, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp04, hp06, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_tune_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp04, hp06, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 3)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 40) := by
  simp only [domL, hostEvolve, mL, acc_tune_limp_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) := by
  simp only [domR, hostEvolve, mR, acc_tune_limp_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 2) : hostEvolve vs 3 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 4) : hostEvolve vs 3 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-! ## The declared rows -/

theorem comps_eq0 : comps 0 =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 2)),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const 2))] := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [comps, hostComps, acc_tune_limp_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp20, ITerm.toHost, Lv, Rv]

theorem comps_eq1 : comps 1 =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 2)),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const (13/2)))] := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [comps, hostComps, acc_tune_limp_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp20, hp65, ITerm.toHost, Lv, Rv]

/-- The row's upper slack: `CRUISE` 2, `LIMP` 6.5. -/
noncomputable def slack (r : ℕ) : ℝ := if r = 0 then 2 else 13/2

theorem eval_g (r : ℕ) (hr : r < 2) (x : State (Var 3)) :
    Term.eval (g r) x = x (Lv 0) - (x (Rv 0) + 2) := by
  interval_cases r
  · simp [g, comps_eq0, Term.eval, AOp.interp]
  · simp [g, comps_eq1, Term.eval, AOp.interp]

theorem eval_gs0 (r : ℕ) (hr : r < 2) (x : State (Var 3)) :
    Term.eval ((gs r).getD 0 (Term.const 0)) x = x (Rv 0) - (x (Lv 0) + slack r) := by
  interval_cases r
  · simp [gs, comps_eq0, Term.eval, AOp.interp, slack]
  · simp [gs, comps_eq1, Term.eval, AOp.interp, slack]

theorem sat_FRow (r : ℕ) (hr : r < 2) (ν : State (Var 3)) :
    Formula.sat (FRow r) ν ↔ (ν (Lv 0) ≤ ν (Rv 0) + 2 ∧ ν (Rv 0) ≤ ν (Lv 0) + slack r) := by
  rw [FRow, sat_FM_iff]
  have h1 := eval_g r hr ν
  have h2 := eval_gs0 r hr ν
  simp only [gs, List.getD_cons_zero] at h2
  constructor
  · intro h
    have a := h (g r) List.mem_cons_self
    have b := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [h1] at a; rw [h2] at b
    constructor <;> linarith
  · rintro ⟨a, b⟩ c hc
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [h1]; linarith
    · rw [h2]; linarith

theorem comps_fv (r : ℕ) (hr : r < 2) : ∀ c ∈ g r :: gs r, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  interval_cases r <;>
  · simp only [g, gs, comps_eq0, comps_eq1, List.getD_cons_zero, List.getD_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · intro x hx
      simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp

/-- Past the declared rows the lookup falls back to `tt`, which has no components. -/
theorem comps_nil (r : ℕ) (hr : 2 ≤ r) : comps r = [] := by
  unfold comps
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [acc_tune_limp_IRv2]; omega)]
  simp [hostComps, Oracle.invComponents]

theorem comps_fv_all (r : ℕ) : ∀ c ∈ g r :: gs r, c.fv ⊆ range Lv ∪ range Rv := by
  by_cases hr : r < 2
  · exact comps_fv r hr
  · intro c hc
    simp only [g, gs, comps_nil r (by omega), List.getD_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hc
    subst hc
    simp [Term.fv]

theorem aux_notin_FRow (a : Fin 3) (r : ℕ) :
    ((Side.Aux, a) : Var 3) ∉ (FRow r).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all r g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The cut families, concretely -/

theorem gL_ge22 : hostAtomG vs 3 Side.L (.cmp ">=" (.var "v") (.num "22.0")) = thrGe (Lv 0) 22 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp220, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gL_le36 : hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num "36.0")) = thrLe (Lv 0) 36 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp360, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_le30 : hostAtomG vs 3 Side.L (.cmp "<=" (.var "v") (.num "30.0")) = thrLe (Lv 0) 30 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp300, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gR_ge20 : hostAtomG vs 3 Side.R (.cmp ">=" (.var "v") (.num "20.0")) = thrGe (Rv 0) 20 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp200, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]
theorem gR_le36 : hostAtomG vs 3 Side.R (.cmp "<=" (.var "v") (.num "36.0")) = thrLe (Rv 0) 36 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp360, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "22.0")), thrGe (Lv 0) 22),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "36.0")), thrLe (Lv 0) 36)] := by
  rw [← gL_ge22, ← gL_le36]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 3 Side.L (.cmp ">=" (.var "v") (.num "22.0")), thrGe (Lv 0) 22),
     (hostAtomF vs 3 Side.L (.cmp "<=" (.var "v") (.num "30.0")), thrLe (Lv 0) 30)] := by
  rw [← gL_ge22, ← gL_le30]; rfl
theorem cR_val (q : ℕ) (hq : q < 3) : cR q =
    [(hostAtomF vs 3 Side.R (.cmp ">=" (.var "v") (.num "20.0")), thrGe (Rv 0) 20),
     (hostAtomF vs 3 Side.R (.cmp "<=" (.var "v") (.num "36.0")), thrLe (Rv 0) 36)] := by
  rw [← gR_ge20, ← gR_le36]; interval_cases q <;> rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 2) :
    ∀ x ∈ cutAtomsOfX acc_tune_limp_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, acc_tune_limp_cutsV2X, mL, acc_tune_limp_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX acc_tune_limp_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, acc_tune_limp_cutsV2X, mR, acc_tune_limp_IRv2] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 2) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 3)) (hiff : AtomsIff cs) (ν : State (Var 3)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 2) :
    ∀ ν, Formula.sat (hostGuard vs 3 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard acc_tune_limp_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, acc_tune_limp_cutsV2X, mL, acc_tune_limp_IRv2] at hx
      rcases hx with rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, acc_tune_limp_cutsV2X, mL, acc_tune_limp_IRv2] at hx
      rcases hx with rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp220, hp300, hp360, vs, Run.resolveVar,
          List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, acc_tune_limp_IRv2, Run.lowerF, Run.lowerE, hp220, hp300, hp360, vs,
        Run.resolveVar, List.findIdx?_cons]

/-! ## Side splits -/

theorem fL_pipe (l : ℕ) (i : Fin 3) : fL l i =
    (((some (mL l)).bind (Run.dynOf vs 3 Side.L)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem fR_pipe (q : ℕ) (i : Fin 3) : fR q i =
    (((some (mR q)).bind (Run.dynOf vs 3 Side.R)).map
      (fun f => ITerm.toHost (f i))).getD (Term.const 0) := rfl
theorem domL_pipe : domL =
    (((some (mL 0)).bind (fun m => Run.lowerF vs 3 Side.L m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl
theorem domR_pipe : domR =
    (((some (mR 0)).bind (fun m => Run.lowerF vs 3 Side.R m.evolve)).map
      IForm.toHost).getD Formula.tt := rfl

theorem hfL (l : ℕ) (hl : l < 2) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, acc_tune_limp_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 4) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, acc_tune_limp_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, acc_tune_limp_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, acc_tune_limp_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 2) : (hostGuard vs 3 Side.L (mL l)).fv ⊆ range Lv :=
  hostGuard_fv_L vs (mL l) (by
    interval_cases l <;>
      simp [mL, acc_tune_limp_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem thr_fv_L (j : Fin 3) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 3) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 2) (hq : q < 3) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv l hl _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv l hl _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  rw [cR_val q hq] at hc
  interval_cases l <;>
    simp only [cL_0, cL_1, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
    rcases ha with rfl | rfl <;>
    first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2 | exact (thr_fv_R _ _).1 |
      exact (thr_fv_R _ _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (NORMAL 0, COMFORT 1, SPORT 2, DISENGAGE 3). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 0), (1, 3), (2, 2), (2, 0), (2, 3), (3, 3)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range acc_tune_limp_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (acc_tune_limp_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 4 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 4) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 4 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 4 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem htt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = Formula.tt := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [edgeW, Gr]

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

/-! ## Regions: the right mode's kept cut atoms; the pruned sink is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 3) :=
  if q < 3 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 3) (ν : State (Var 3)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region3 (ν : State (Var 3)) : ¬ Formula.sat (region 3) ν := by
  simp [region, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h3 : q < 3
  · simp only [region, h3, if_true]
    intro x hx
    unfold cutF at hx
    have key : ∀ (L : List (CutAtomP 3)) (acc : Formula (Var 3)),
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
    rw [cR_val q h3] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h3, if_false]
    simp [Formula.fv, Term.fv]

/-! ## The stretch of each left window (the emitted cover's λ) -/

/-- `CRUISE` at `λ = 3/2`, `LIMP` at `λ = 1` (`BenchCovers/acc_tune_limp.lean`). -/
noncomputable def lam (l : ℕ) : ℝ := if l = 0 then 3/2 else 1

theorem lam_pos (l : ℕ) : 0 < lam l := by unfold lam; split_ifs <;> norm_num

/-! ## O2: the kept atoms stay along the joint flows (threshold atoms, rational) -/

theorem stayL (l q : ℕ) (hl : l < 2) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 22 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [fL0_eval_C]; linarith) hinit
    · exact boxle_thrLe_L 0 36 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [fL0_eval_C]; linarith) hinit
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 22 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [fL0_eval_L]; linarith) hinit
    · exact boxle_thrLe_L 0 30 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ hz => by rw [fL0_eval_L]; linarith) hinit

theorem stayR (l q : ℕ) (hq : q < 3) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const (lam l))) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hf := fR0_eval q hq
  have hc := le_of_lt (lam_pos l)
  have hk := kR_pos q
  rw [cR_val q hq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact boxle_thrGe_R 0 20 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; exact mul_nonneg hk.le (by linarith)) hinit
  · exact boxle_thrLe_R 0 36 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [hf]; exact mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)) hinit

/-! ## Existence: every non-sink right mode is a contraction toward a set point in `[0, 40]` -/

theorem hwfB (l q : ℕ) (hq : q < 3) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const (lam l)) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lam l * kR q) 30)
    (lam := Term.const 1) (domR := bandDom 0 0 40) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval q hq]
        ring
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval q hq]
        simp [Term.eval]
    | 2 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR2_eval q hq]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (lam l * kR q) 30 0 40 dt ?_ ?_ ?_
    · exact mul_nonneg (le_of_lt (lam_pos l)) (kR_pos q).le
    · norm_num
    · norm_num

theorem es (l q : ℕ) (hq : q < 3) (dt : ℝ) (A : Formula (Var 3)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const (lam l)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  refine hExistSegB_of_wellFormedFlowB (fL l) (fR q) _ domL domR dt _ (hwfB l q hq dt) ?_ ?_
  · intro x hx hb
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL l) _ hb
    obtain ⟨j, hj⟩ := hdomR hx
    rw [← hj] at hi
    exact absurd hi (by simp [Lv, Rv, Prod.ext_iff])
  · have htgd : tg ∉ domR.fv := by
      intro h
      obtain ⟨i, hi⟩ := hdomR h
      exact absurd hi (by simp [Rv, Prod.ext_iff])
    rw [(Formula.coincidence domR (fun v hv =>
      Function.update_of_ne (fun hc => htgd (by rw [← hc]; exact hv)) _ _) :
        Formula.sat domR _ ↔ Formula.sat domR σ)]
    exact hσ.2.2

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l` at ITS OWN row (`invRow = l`), right mode `q`, at the cover's
λ and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX acc_tune_limp_IRv2 acc_tune_limp_cutsV2X 3 l [0, 1] (lam l) l q

theorem verd_core (l q : ℕ) (hl : l < 2) (hq : q < 4) (h : Verd l q) :
    VerdXCore (g l :: gs l) (fL l) (fR q) (lam l)
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

theorem couple (l q : ℕ) (hl : l < 2) (hq : q < 3) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fL l) (fR q) (lam l) (lam_pos l)
    domL domR 1 dt
    (hfL l hl) (hfR q (by omega)) hdomL hdomR (anchor_fv l q hl hq) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR q hq) (stayL l q hl) (stayR l q hq)
    (verd_core l q hl (by omega) hv) (es l q hq dt _)

theorem sat_faModal_monoPost {P Q : Program (Var 3)} {A B : Formula (Var 3)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 3)}
    (h : Formula.sat (faModal (Equiv.refl (Var 3)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l qs : ℕ) (hl : l < 2) (hqs : qs < 3) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FRow l) env) (region qs))) σ := by
  have htgF : tg ∉ (FM (g l) (gs l ++ atomTerms (cL l) (cR qs))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l qs hl hqs g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM (g l) (gs l ++ atomTerms (cL l) (cR qs)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 3)))
    (by
      intro h hh
      simp at hh)
    (fun σ' hσ' => hσ'.2.1)
    (by
      intro h hh
      simp at hh)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR qs) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR qs, Term.const 1, domR⟩ : RepoHop 3)
        (hfR qs (by omega)) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l qs hl hqs dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 3))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append (g l) (gs l) _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR qs hqs) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt qs hqs ν).mpr hRν⟩

/-! ## The left automaton, from the file -/

/-- Left mode `l`'s window: re-test its guard, then the clock-capped window. -/
noncomputable def gw (dt : ℝ) (l : ℕ) : Program (Var 3) :=
  gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1

/-- The file's `next` lists, resolved to indices. -/
def nextL : List (List ℕ) :=
  (List.range 2).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex acc_tune_limp_IRv2))

/-- `CRUISE → [CRUISE, LIMP]`, `LIMP → [LIMP]`. -/
theorem nextL_eq : nextL = [[0, 1], [1]] := by decide

theorem nextL_transitions :
    ((List.range 2).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions acc_tune_limp_IRv2 := by decide

noncomputable def A (dt : ℝ) : LeftAut 3 :=
  { windows := [gw dt 0, gw dt 1],
    guards := [hostGuard vs 3 Side.L (mL 0), hostGuard vs 3 Side.L (mL 1)],
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 2 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 2) : (A dt).window t = gw dt t := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 2) :
    (A dt).guard t = hostGuard vs 3 Side.L (mL t) := by
  interval_cases t <;> rfl

theorem A_succ (dt : ℝ) (m' : ℕ) : (A dt).succ m' = nextL.getD m' [] := rfl

theorem hnext (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', t < (A dt).numModes := by
  intro m' hm' t ht
  rw [A_numModes] at hm' ⊢
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht <;> omega

theorem hgrd (dt : ℝ) : ∀ t < (A dt).numModes, ((A dt).guard t).fv ⊆ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_guard dt t ht]
  exact hguardL t ht

theorem hwin (dt : ℝ) : ∀ t < (A dt).numModes,
    Program.vars ((A dt).window t) ⊆ {((Side.Aux, 1) : Var 3)} ∪ range Lv := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  exact vars_gwindowSegL_sub _ (fL t) domL 1 dt 1 (hguardL t ht) (hfL t ht) hdomL

/-! ## Freshness of `u_L` -/

theorem hmvenv : mv ∉ env.fv := by
  rintro (h | h)
  · exact aux_notin_range_Lv 0 (hdomL h)
  · exact aux_notin_range_Rv 0 (hdomR h)

theorem hmvreg : ∀ q, mv ∉ (region q).fv := fun q h => aux_notin_range_Rv 0 (region_fv q h)

theorem hulenv : uL ∉ env.fv := by
  rintro (h | h)
  · exact aux_notin_range_Lv 2 (hdomL h)
  · exact aux_notin_range_Rv 2 (hdomR h)

theorem hulBk : uL ∉ (mvRegion mv region Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region Gr.modes.length (fun q _ => region_fv q) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 2
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 2
  · rw [A_window dt t ht]
    refine framesMv_gwindow _ (fL t) domL tg dt 1 uL (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
    exact aux_ne_Lv 2 i hi
  · have : (A dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulR : uL ∉ (rightAutomatonBody Gr mv).bv :=
  notMem_bv_rightAutomatonBody Gr mv uL (by decide) (aux_notin_range_Rv 2) htt hRv

/-! ## The handoff: nested rows, in-kernel -/

theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  interval_cases m' <;> simp at ht
  · rcases ht with rfl | rfl
    · exact hF
    · -- CRUISE → LIMP: same lower conjunct; `v_R ≤ v_L + 2` implies `v_R ≤ v_L + 6.5`
      rw [sat_FRow 0 (by norm_num)] at hF
      rw [sat_FRow 1 (by norm_num)]
      simp only [slack] at hF ⊢
      norm_num at hF ⊢
      constructor <;> linarith [hF.1, hF.2]
  · subst ht; exact hF

/-! ## The per-mode steps: stay in the certified start mode -/

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 3)) (ψ : Formula (Var 3))
    {σ : State (Var 3)}
    (hbody : Formula.sat (hostGuard vs 3 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 3))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3)) (gw dt l) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (l q : ℕ) (hl : l < 2) (hq : q < 3) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 3)} (hσ : Formula.sat (Formula.and (FRow l) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 3)) (gw dt l)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FRow l) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨Gr_modeAt q (by omega), edge_mem q q ?_⟩
    interval_cases q <;> simp [edgeList]
  · refine gate l dt _ _ (fun hguard => ?_)
    have hanchor : Formula.sat (Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q)))
        (Formula.and domL domR)) σ := by
      refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
      exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
        ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
    have := respond l q hl hq dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

theorem HmultiT (l : ℕ) (hl : l < 2) (dt : ℝ)
    (h0 : Verd l 0) (h1 : Verd l 1) (h2 : Verd l 2) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FRow l) env) (region q)) σ →
      ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 3)) (gw dt l)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FRow l) env) (region (qfOf segs q)))) σ := by
  intro q hq σ _ hσ
  rw [Gr_len] at hq
  match q, hq with
  | 0, _ => exact stayCase l 0 hl (by norm_num) dt h0 hσ.1 hσ.2
  | 1, _ => exact stayCase l 1 hl (by norm_num) dt h1 hσ.1 hσ.2
  | 2, _ => exact stayCase l 2 hl (by norm_num) dt h2 hσ.1 hσ.2
  | 3, _ => exact absurd hσ.2 (not_sat_region3 σ)

theorem hstepM (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2) :
    ∀ t < (A dt).numModes, ∀ σ,
    Formula.sat (Formula.and (Formula.and (FRow t) env)
      (mvRegion mv region Gr.modes.length)) σ →
    Formula.sat (faModal (Equiv.refl (Var 3)) ((A dt).window t)
      (Program.star (rightAutomatonBody Gr mv))
      (Formula.and (Formula.and (FRow t) env)
        (mvRegion mv region Gr.modes.length))) σ := by
  intro t ht
  rw [A_numModes] at ht
  rw [A_window dt t ht]
  have hframe : FramesMv (gw dt t) mv := by
    refine framesMv_gwindow _ (fL t) domL tg dt 1 mv (by decide) ?_
    intro h
    obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
    exact aux_ne_Lv 0 i hi
  interval_cases t
  · exact hstepMode_multiR Gr mv (FRow 0) env region _ (aux_notin_FRow 0 0)
      hmvenv hmvreg hfresh htt hlt hframe (HmultiT 0 (by norm_num) dt h00 h01 h02)
  · exact hstepMode_multiR Gr mv (FRow 1) env region _ (aux_notin_FRow 0 1)
      hmvenv hmvreg hfresh htt hlt hframe (HmultiT 1 (by norm_num) dt h10 h11 h12)

/-! ## The composed theorem -/

/-- **`acc_tune_limp` (suite_v2), Theorem 3 at the DECLARED mode-dependent invariant.**
`u_L`-keyed: the `CRUISE` window at `|v_L − v_R| ≤ 2`, the `LIMP` window at
`v_L ≤ v_R + 2 ∧ v_R ≤ v_L + 6.5`, over the left automaton of the file
(`CRUISE → [CRUISE, LIMP]`, `LIMP → [LIMP]`; each window re-tests its mode's guard), against
the four-mode right automaton of the file (declared edges, the pruned `→ DISENGAGE` edges
included). The loop invariant also carries the evolve envelope `0 ≤ v ≤ 40` on both sides
and the right mode's region — its kept cut atoms (`20 ≤ v_R ≤ 36` in `NORMAL`, `COMFORT`,
`SPORT`), `DISENGAGE` excluded (the pruned sink: the right is never in it). Response: STAY in
the start mode on the certified joint segment at the cover's λ (3/2 for `CRUISE`, 1 for
`LIMP`); the left atoms (`CRUISE`: `22 ≤ v_L ≤ 36`, `LIMP`: `22 ≤ v_L ≤ 30`) come from the
window's guard (O1) and stay along the flow from the field's sign (rational, Z3-free).
Handoffs (in-kernel): `CRUISE → LIMP` keeps `v_L ≤ v_R + 2` and loosens the upper slack 2 to
6.5, self-loops are trivial. Residuals: six stratified verdict packs `Verd l q`
(`l ∈ {CRUISE, LIMP}`, `q ∈ {NORMAL, COMFORT, SPORT}`) over the cut-narrowed domains
(`modalVerdX` at `invRow = l`, the tool's own queries). -/
theorem acc_tune_limp_modeKeyed (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody Gr mv)
      (psiK uL ϕRow (A dt).numModes domL domR (mvRegionR mv region Gr.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL Gr mv FRow ϕRow domL domR
    (mvRegion mv region Gr.modes.length) (mvRegionR mv region Gr.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) htt hRv
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody Gr mv) FRow env
      (mvRegion mv region Gr.modes.length)
      (aux_notin_FRow 2)
      hulenv hulBk (hulG dt)
      (hframesUl dt) hulR (hnext dt) (hstepM dt h00 h01 h02 h10 h11 h12) (handoff dt)
  · exact hddF_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv region Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) htt hRv
      (fun m hm => canonInvM_varsL (g m) (gs m) (comps_fv m hm))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv region Gr.modes.length (fun q _ => region_fv q) hv)

end V2AccTuneLimp
end RelCertifier

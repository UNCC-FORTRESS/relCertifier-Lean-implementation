/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice exhibit) — modal Theorem 3 with a chosen right mode

Velocity `v ∈ [0, 30]`, three acceleration modes on each side (`Accel` +1, `Coast` 0, `Brake`
−1), every mode a declared successor of every mode, the right's guards wider than the left's by
the tolerance. Claim: `|v_L − v_R| ≤ 1`. The right must COPY the left's mode. Response: a
zero-duration hop into the left's mode (legal: the left's guard and the claim put the right in
the wider right guard), then the certified joint segment in that mode for the whole window,
then a switch into `Coast`, whose guard is the whole envelope.

Standalone: the response is written here, not replayed from the tool's choice cover; the
generated bridge instance `Bridge/VehicleAccelCopy.lean` replays the emitted chosen sets.
Existence of the right segment holds from the start state only (the right guard and one control
period, `dt ≤ 1`), so the coupling is the pointwise one (`couple_cutX_at`).
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Choice.Cuts.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.ConstMirror
import RelCertifier.InstancesV2.Choice.PointwiseCouple

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceVehicleAccelCopy

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := vehicle_accel_copy_IRc.L.modes.getD l dm
def mR (q : ℕ) : PMode := vehicle_accel_copy_IRc.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

/-- The declared invariant's components (row 0; every row is the same). -/
noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (vehicle_accel_copy_IRc.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := [comps.getD 1 (Term.const 0)]

noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX vehicle_accel_copy_cutsCX.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX vehicle_accel_copy_cutsCX.R (mR q).name)

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp270 : Run.parseRat "27.0" = some (27 : ℚ) := by
  have h : parseQ "27.0" = some (⟨270, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp1 : Run.parseRat "1" = some (1 : ℚ) := by
  have h : parseQ "1" = some (⟨1, 1⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## Evaluations of the lowered data -/

/-- The accelerations, by mode index. -/
noncomputable def acc : ℕ → ℝ
  | 0 => 1 | 1 => 0 | _ => -1

/-- The guard bounds, by mode index (left; the right's are wider by the tolerance). -/
noncomputable def loL : ℕ → ℝ
  | 0 => 0 | 1 => 0 | _ => 5
noncomputable def hiL : ℕ → ℝ
  | 0 => 25 | _ => 30
noncomputable def loR : ℕ → ℝ
  | 0 => 0 | 1 => 0 | _ => 3
noncomputable def hiR : ℕ → ℝ
  | 0 => 27 | _ => 30

/-- The coordinate field: the acceleration on index 0, the padding index frozen. -/
noncomputable def cf (q : ℕ) : Fin 2 → ℝ := fun i => if i = 0 then acc q else 0

theorem fL_eval (l : ℕ) (hl : l < 3) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fL l i) x = cf l i := by
  fin_cases i <;> interval_cases l <;>
    simp [fL, hostDyn, mL, vehicle_accel_copy_IRc, vs, Run.dynOf, Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, cf, acc] <;> norm_num

theorem fR_eval (q : ℕ) (hq : q < 3) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fR q i) x = cf q i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mR, vehicle_accel_copy_IRc, vs, Run.dynOf, Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cf, acc] <;> norm_num

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 30) := by
  simp only [domL, hostEvolve, mL, vehicle_accel_copy_IRc, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp300, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 30) := by
  simp only [domR, hostEvolve, mR, vehicle_accel_copy_IRc, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp300, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 3) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 3) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.binop .add (Term.var (Rv 0)) (Term.const 1)),
     Term.binop .sub (Term.var (Rv 0)) (Term.binop .add (Term.var (Lv 0)) (Term.const 1))] := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [comps, hostComps, vehicle_accel_copy_IRc, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, hp1, ITerm.toHost, Lv, Rv]

/-- Every invariant row is row 0. -/
theorem comps_row (l : ℕ) (hl : l < 3) :
    hostComps vs 2 (vehicle_accel_copy_IRc.invariants.getD l ("", PForm.tt)).2 = comps := by
  interval_cases l <;> rfl

theorem sat_FMgs (x : State (Var 2)) :
    Formula.sat (FM g gs) x ↔ (x (Lv 0) ≤ x (Rv 0) + 1 ∧ x (Rv 0) ≤ x (Lv 0) + 1) := by
  rw [sat_FM_iff]
  simp [g, gs, comps_eq, Term.eval, AOp.interp]
  all_goals (constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith)

/-! ## The cut families, concretely -/

/-- The kept cuts of mode `q` (the same on both sides), as a predicate on the velocity. -/
def cutP : ℕ → ℝ → Prop
  | 0, v => 0 ≤ v
  | 1, v => 0 ≤ v ∧ v ≤ 30
  | _, v => v ≤ 30

theorem gL_le30 : hostAtomG vs 2 Side.L (.cmp "<=" (.var "v") (.num "30.0")) = thrLe (Lv 0) 30 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp300, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_ge0 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")) = thrGe (Lv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gR_le30 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "v") (.num "30.0")) = thrLe (Rv 0) 30 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp300, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]
theorem gR_ge0 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")) = thrGe (Rv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]

theorem cL_0 : cL 0 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Lv 0) 0)] := by
  rw [← gL_ge0]; rfl
theorem cL_1 : cL 1 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Lv 0) 0),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "v") (.num "30.0")), thrLe (Lv 0) 30)] := by
  rw [← gL_ge0, ← gL_le30]; rfl
theorem cL_2 : cL 2 =
    [(hostAtomF vs 2 Side.L (.cmp "<=" (.var "v") (.num "30.0")), thrLe (Lv 0) 30)] := by
  rw [← gL_le30]; rfl
theorem cR_0 : cR 0 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Rv 0) 0)] := by
  rw [← gR_ge0]; rfl
theorem cR_1 : cR 1 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Rv 0) 0),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "v") (.num "30.0")), thrLe (Rv 0) 30)] := by
  rw [← gR_ge0, ← gR_le30]; rfl
theorem cR_2 : cR 2 =
    [(hostAtomF vs 2 Side.R (.cmp "<=" (.var "v") (.num "30.0")), thrLe (Rv 0) 30)] := by
  rw [← gR_le30]; rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 3) :
    ∀ x ∈ cutAtomsOfX vehicle_accel_copy_cutsCX.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  interval_cases l <;>
    simp [cutAtomsOfX, vehicle_accel_copy_cutsCX, mL, vehicle_accel_copy_IRc] at hx <;>
    (try rcases hx with rfl | rfl) <;> (try subst hx) <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 3) :
    ∀ x ∈ cutAtomsOfX vehicle_accel_copy_cutsCX.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  interval_cases q <;>
    simp [cutAtomsOfX, vehicle_accel_copy_cutsCX, mR, vehicle_accel_copy_IRc] at hx <;>
    (try rcases hx with rfl | rfl) <;> (try subst hx) <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 3) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 3) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 2)) (hiff : AtomsIff cs) (ν : State (Var 2)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatL_val (l : ℕ) (hl : l < 3) (ν : State (Var 2)) :
    CutSat (cL l) ν ↔ cutP l (ν (Lv 0)) := by
  rw [cutSat_iff _ (hiffL l hl)]
  interval_cases l
  · rw [cL_0]; simp [cutP, thrGe, Term.eval, AOp.interp]
  · rw [cL_1]; simp [cutP, thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_2]; simp [cutP, thrLe, Term.eval, AOp.interp]

theorem cutSatR_val (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    CutSat (cR q) ν ↔ cutP q (ν (Rv 0)) := by
  rw [cutSat_iff _ (hiffR q hq)]
  interval_cases q
  · rw [cR_0]; simp [cutP, thrGe, Term.eval, AOp.interp]
  · rw [cR_1]; simp [cutP, thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_2]; simp [cutP, thrLe, Term.eval, AOp.interp]

/-- The envelope implies every mode's kept cuts. -/
theorem cutP_of_env (q : ℕ) (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 30) : cutP q v := by
  match q with
  | 0 => exact h0
  | 1 => exact ⟨h0, h1⟩
  | _ + 2 => exact h1

theorem sat_guardL (l : ℕ) (hl : l < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔ (loL l ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ hiL l) := by
  interval_cases l <;>
    simp [hostGuard, mL, vehicle_accel_copy_IRc, Run.lowerF, Run.lowerE, hp00, hp250, hp300,
      hp50, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Lv, loL, hiL]

theorem sat_guardR (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ (loR q ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ hiR q) := by
  interval_cases q <;>
    simp [hostGuard, mR, vehicle_accel_copy_IRc, Run.lowerF, Run.lowerE, hp00, hp270, hp300,
      hp30, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Rv, loR, hiR]

/-- **The copy is enabled**: the left's guard and the claim put the right in the right's
guard of the same mode (the right's guards are wider by the tolerance). -/
theorem guardR_of_guardL (l : ℕ) (hl : l < 3) (ν : State (Var 2))
    (hF : Formula.sat (FM g gs) ν) (hR : Formula.sat domR ν)
    (hgL : Formula.sat (hostGuard vs 2 Side.L (mL l)) ν) :
    Formula.sat (hostGuard vs 2 Side.R (mR l)) ν := by
  have hc := (sat_FMgs ν).mp hF
  have hd := (sat_domR ν).mp hR
  have hg := (sat_guardL l hl ν).mp hgL
  rw [sat_guardR l hl]
  interval_cases l <;> simp only [loL, hiL, loR, hiR] at hg ⊢ <;> constructor <;> linarith
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

theorem hfL (l : ℕ) (hl : l < 3) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, vehicle_accel_copy_IRc, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 3) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, vehicle_accel_copy_IRc, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, vehicle_accel_copy_IRc, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, vehicle_accel_copy_IRc, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 3) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
        simp [mL, vehicle_accel_copy_IRc, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

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

theorem anchor_fv (l q : ℕ) (hl : l < 3) (hq : q < 3) :
    ∀ c ∈ g :: gs ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, List.map_append, List.mem_append, List.mem_map] at hc
  have hLa : ∀ a ∈ cL l, a.2.fv ⊆ range Lv ∪ range Rv := by
    intro a ha
    interval_cases l <;>
      simp only [cL_0, cL_1, cL_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2
  have hRa : ∀ a ∈ cR q, a.2.fv ⊆ range Lv ∪ range Rv := by
    intro a ha
    interval_cases q <;>
      simp only [cR_0, cR_1, cR_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      first | exact (thr_fv_R _ _).1 | exact (thr_fv_R _ _).2
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact hLa a ha
  · exact hRa a ha

/-! ## The right automaton (the file's modes; every mode a successor of every mode) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

def edgeList : List (ℕ × ℕ) :=
  (List.range 3).flatMap (fun s => (List.range 3).map (fun t => (s, t)))

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range vehicle_accel_copy_IRc.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (vehicle_accel_copy_IRc.R.modes.findIdx (·.name == nm))))) := by
  decide

theorem edgeList_mem (s t : ℕ) (hs : s < 3) (ht : t < 3) : (s, t) ∈ edgeList := by
  simp [edgeList, hs, ht]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 3 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem hguardR (q : ℕ) (hq : q < 3) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;>
      simp [mR, vehicle_accel_copy_IRc, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 3 := by decide

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact edgeList_tgt p hp

theorem hRv : ∀ q m, Gr.modeAt q = some m →
    m.sys.boundSet ∪ m.sys.readVars ∪ m.dom.fv ⊆ range Rv := by
  intro q m hm
  obtain ⟨hq, rfl⟩ := Gr_modeAt_inv hm
  intro y hy
  rcases hy with (hy | hy) | hy
  · exact rightBlock_boundSet_sub (fR q) (Term.const 1) hy
  · exact rightBlock_readVars_sub (fR q) (Term.const 1) (hfR q hq) (by simp [Term.fv]) hy
  · exact hdomR hy

theorem edge_mem (s t : ℕ) (hs : s < 3) (ht : t < 3) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), edgeList_mem s t hs ht, rfl⟩, by simp [edgeW]⟩

theorem hfresh : ∀ q m, Gr.modeAt q = some m → mv ∉ (Program.ode m.sys m.dom).fv := by
  intro q m hm hmv
  exact aux_notin_range_Rv 0 (hRv q m hm (vars_ode_sub _ _ (Or.inl hmv)))

theorem Gr_guards : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.guard = hostGuard vs 2 Side.R (mR e.tgt) := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, -, rfl⟩ := hmem
  rfl

theorem hgR : GuardsRight Gr := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  exact hguardR p.2 (edgeList_tgt p hp)

/-! ## Regions: the right mode's kept cut atoms -/

noncomputable def region (q : ℕ) : Formula (Var 2) :=
  if q < 3 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h3 : q < 3
  · simp only [region, h3, if_true]
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
    interval_cases q <;>
      simp only [cR_0, cR_1, cR_2, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h3, if_false]
    simp [Formula.fv, Term.fv]

noncomputable def gregion (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vs 2 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [vehicle_accel_copy_IRc, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q)

/-! ## The certified pairings: each left mode with the same right mode, stretch 1 -/

noncomputable def lam (_l _q : ℕ) : ℝ := 1

theorem lam_pos (l q : ℕ) : 0 < lam l q := by unfold lam; norm_num

/-- O2: the kept atoms stay along the joint flow of a pairing `(l, l)` (constant fields
pointing inward at each kept threshold). -/
theorem stayL (l : ℕ) (hl : l < 3) :
    AtomsStayC (cL l) (jointSys (fL l) (fR l) (Term.const (lam l l)))
      (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hf : ∀ z, Term.eval (fL l 0) z = acc l := fun z => by rw [fL_eval l hl]; simp [cf]
  interval_cases l
  · rw [cL_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cL_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
    · exact boxle_thrLe_L 0 30 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_L 0 30 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit

theorem stayR (l : ℕ) (hl : l < 3) :
    AtomsStayC (cR l) (jointSys (fL l) (fR l) (Term.const (lam l l)))
      (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR l hl a ha ν).mp (hν a ha)
  have hf : ∀ z, Term.eval (fR l 0) z = acc l := fun z => by rw [fR_eval l hl]; simp [cf]
  have hc := le_of_lt (lam_pos l l)
  interval_cases l
  · rw [cR_0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cR_1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
    · exact boxle_thrLe_R 0 30 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_R 0 30 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit

/-! ## Existence from the start: the right guard and one control period -/

/-- From a start in the right guard of `l`, the right run of `l` stays in `[0, 30]` for one
control period (`Accel` from at most 27, `Brake` from at least 3). -/
theorem exist_at (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : dt ≤ 1) {σ : State (Var 2)}
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR l)) σ) :
    HExistSegB (fL l) (fR l) (Term.const (lam l l)) domL domR dt (Function.update σ tg 0) := by
  have hg := (sat_guardR l hl σ).mp hgR
  refine hExistSegB_constRight (fL l) (fR l) _ domL domR dt _ (cf l) (fR_eval l hl)
    (fun _ => by simp [Term.eval, lam]) ?_
  intro t ht0 htdt y hy
  have hy0 := hy 0
  have hνR : Function.update σ tg 0 (Rv 0) = σ (Rv 0) :=
    Function.update_of_ne (by simp [Rv, tg]) _ _
  rw [hνR] at hy0
  simp only [cf, if_true] at hy0
  rw [sat_domR, hy0]
  interval_cases l <;> simp only [loR, hiR, acc] at hg ⊢ <;> constructor <;> nlinarith

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left mode `l`, right mode `l` (the chosen one), stretch 1, strata order
`[0, 1]`, the invariant row of `l`. -/
def Verd (l : ℕ) : Prop :=
  modalVerdX vehicle_accel_copy_IRc vehicle_accel_copy_cutsCX 2 l [0, 1] (lam l l) l l

theorem verd_core (l : ℕ) (hl : l < 3) (h : Verd l) :
    VerdXCore (g :: gs) (fL l) (fR l) (lam l l)
      (domCutX (Formula.and domL domR) (cL l) (cR l)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  have hvs : vehicle_accel_copy_IRc.L.stateVars = vs := rfl
  simp only [hvs, comps_row l hl] at h'
  rw [← domL_univ l hl, ← domR_univ l hl]
  exact h'

/-! ## The coupling at the start, the window response -/

theorem couple (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : dt ≤ 1) (hv : Verd l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ)
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR l)) σ) :
    faModalB (Equiv.refl (Var 2))
      (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
      (Program.ode (rightBlock (fR l) (Term.const 1)) domR)
      (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l))) (Formula.and domL domR))
      tg dt (Function.update σ tg 0) :=
  couple_cutX_at g gs (g :: gs) (cL l) (cR l) (fL l) (fR l) (lam l l) (lam_pos l l) domL domR 1
    dt (hfL l hl) (hfR l hl) hdomL hdomR (anchor_fv l l hl hl) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR l hl) (stayL l hl) (stayR l hl)
    (verd_core l hl hv) hσ (exist_at l hl dt hdt hgR)

theorem respond (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : dt ≤ 1) (hv : Verd l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ)
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR l)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq [Program.ode (rightBlock (fR l) (Term.const 1)) domR])
      (Formula.and (Formula.and (FM g gs) env) (region l))) σ := by
  have hw := window_of_faModalB (leftBlock (fL l)) domL _ _ tg dt (couple l hl dt hdt hv hσ hgR)
  rw [faModal_sat] at hw ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := hw ν hν
  refine ⟨μ, hμ, ?_⟩
  obtain ⟨hFμ, hatμ⟩ := (sat_FM_append g gs _ μ).mp hA.1
  obtain ⟨-, hRμ⟩ := (atomTerms_iff (hiffL l hl) (hiffR l hl) μ).mp hatμ
  exact ⟨⟨hFμ, hA.2⟩, (sat_region_lt l hl μ).mpr hRμ⟩

/-! ## The windows -/

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  (List.range 3).map (fun l => (hostGuard vs 2 Side.L (mL l), fL l, domL, 1))

noncomputable def leftProgs (dt : ℝ) : List (Program (Var 2)) :=
  leftData.map (fun d => gwindowSeg d.1 (leftBlock d.2.1) d.2.2.1 tg dt d.2.2.2)

theorem hL : ∀ d ∈ leftData, d.1.fv ⊆ range Lv ∧
    (∀ i, (d.2.1 i).fv ⊆ range Lv) ∧ d.2.2.1.fv ⊆ range Lv := by
  intro d hd
  simp only [leftData, List.mem_map, List.mem_range] at hd
  obtain ⟨l, hl, rfl⟩ := hd
  exact ⟨hguardL l hl, hfL l hl, hdomL⟩

theorem hframes (dt : ℝ) : ∀ P ∈ leftProgs dt, FramesMv P mv := by
  intro P hP
  simp only [leftProgs, List.mem_map] at hP
  obtain ⟨d, hd, rfl⟩ := hP
  refine framesMv_gwindow d.1 d.2.1 d.2.2.1 tg dt d.2.2.2 mv (by decide) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub d.2.1 _ h
  exact aux_ne_Lv 0 i hi

/-- **Nonblocking**: at the end of any response the right is in the envelope, where `Coast`'s
guard (the whole envelope) and `Coast`'s kept cuts hold. -/
theorem nonblock (q : ℕ) (hq : q < 3) :
    NonblockingAt Gr q (Formula.and (Formula.and (FM g gs) env) (region q))
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) := by
  intro μ ⟨hFe, _⟩
  have hR := (sat_domR μ).mp hFe.2.2
  refine ⟨edgeW q 1, edge_mem q 1 hq (by norm_num), ?_, hFe, ?_⟩
  · exact (sat_guardR 1 (by norm_num) μ).mpr (by simp [loR, hiR]; exact hR)
  · exact (sat_region_lt 1 (by norm_num) μ).mpr
      ((cutSatR_val 1 (by norm_num) μ).mpr (cutP_of_env 1 _ hR.1 hR.2))

theorem flowCase (l : ℕ) (hl : l < 3) (dt : ℝ) (hdt : dt ≤ 1) (hv : Verd l) {σ : State (Var 2)}
    (hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ)
    (hgR : Formula.sat (hostGuard vs 2 Side.R (mR l)) σ) :
    GResp Gr l (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ :=
  gresp_final (Gr_modeAt l hl) (respond l hl dt hdt hv hanchor hgR) (nonblock l hl)

theorem anchor_of_loop (l : ℕ) (hl : l < 3) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) :
    Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
      (Formula.and domL domR)) σ := by
  have hL0 := (sat_domL σ).mp hσ.2.1
  have hR0 := (sat_domR σ).mp hσ.2.2
  refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffR l hl) σ).mpr
    ⟨(cutSatL_val l hl σ).mpr (cutP_of_env l _ hL0.1 hL0.2),
     (cutSatR_val l hl σ).mpr (cutP_of_env l _ hR0.1 hR0.2)⟩

/-- **The copy.** From any right start mode `q`, after the left run the right hops into the
left's mode `l` (enabled: `guardR_of_guardL`; the left run does not move the right), then
runs the certified segment of `l`. -/
theorem hopCase (l q : ℕ) (hl : l < 3) (hq : q < 3) (dt : ℝ) (hdt : dt ≤ 1) (hv : Verd l)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hframesR := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
  have hgR := guardR_of_guardL l hl σ hσ.1 hσ.2.2 hguard
  by_cases hql : q = l
  · subst hql
    exact flowCase q hl dt hdt hv (anchor_of_loop q hl hσ) hgR
  · refine gresp_hop (Gr_modeAt q hq) (edge_mem q l hq hl) ?_
      (flowCase l hl dt hdt hv (anchor_of_loop l hl hσ) hgR)
    intro ν hrun
    exact ⟨frames_right hframesR hdomR hrun hσ.2.2, frames_right hframesR (hguardR l hl) hrun hgR⟩

theorem Hmulti (dt : ℝ) (hdt : dt ≤ 1) (hv : ∀ l < 3, Verd l) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ →
      Formula.sat (hostGuard vs 2 Side.R (mR q)) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ _ _
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_map, List.mem_map, List.mem_range] at hP
  obtain ⟨l, hl, rfl⟩ := hP
  exact hopCase l q hl hq dt hdt (hv l hl) hσ

/-! ## Theorem 3 -/

/-- **`vehicle_accel_copy` (choice exhibit), modal Theorem 3 at the declared invariant
`|v_L − v_R| ≤ 1`**, for windows of at most one control period (`dt ≤ 1`, the file's
`epsilon`). Left: the three guard-gated windows; right: the three-mode guarded automaton of the
file. The response copies the left's mode (a zero-duration hop when the right starts
elsewhere), runs the certified joint segment there, and switches into `Coast`. Residuals:
three stratified verdict packs, one per diagonal pairing (`modalVerdX`, the tool's own
queries). -/
theorem vehicle_accel_copy_modal (dt : ℝ) (hdt : dt ≤ 1) (hv : ∀ l < 3, Verd l) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs dt))
      (rightAutomatonBody Gr mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv gregion Gr.modes.length))) := by
  have hmvF : mv ∉ (FM g gs).fv := notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have hmvenv : mv ∉ env.fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 0 (hdomL h)
    · exact aux_notin_range_Rv 0 (hdomR h)
  have hmvreg : ∀ q, mv ∉ (gregion q).fv := by
    intro q
    refine notMem_regionG_fv (fun h => aux_notin_range_Rv 0 (hguardR_all q h)) ?_
    intro h
    exact aux_notin_range_Rv 0 (region_fv q h)
  refine theorem3_faithful_multiR_LR Gr mv (FM g gs) domL domR gregion
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
  · exact hstep_assembled_GR Gr mv (FM g gs) env gregion (leftProgs dt) hmvF hmvenv hmvreg
      hfresh (guardsFresh_of_right Gr 0 hgR) hlt (hframes dt)
      (Hmulti_regionG Gr mv _ region Gr_guards (FM g gs) env (leftProgs dt)
        (fun P hP q hq σ ν hrun => by
          simp only [leftProgs, List.mem_map] at hP
          obtain ⟨d, hd, rfl⟩ := hP
          exact frames_right (vars_gwindowSegL_sub d.1 d.2.1 d.2.2.1 1 dt d.2.2.2 (hL d hd).1
            (hL d hd).2.1 (hL d hd).2.2) (hguardR_all q) hrun)
        (fun P hP q hq σ hmv hσ hg hreg =>
          Hmulti dt hdt hv P hP q hq σ hmv hσ hg hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q _ => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end ChoiceVehicleAccelCopy
end RelCertifier

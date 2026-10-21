/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` (choice exhibit) — modal Theorem 3 with a chosen right mode

Velocity `v ∈ [0, 0.6]`, five acceleration modes on each side (`Am4 Am2 A0 Ap2 Ap4`, constant
accelerations `−0.04 … 0.04`), every mode a declared successor of every mode, the right a copy
of the left. Claim: `v_L = v_R`. From a right start mode other than the left's, no single right
flow keeps the claim, so the all-successors cover declines; the right must CHOOSE the left's
mode. Response: a zero-duration hop into the left's mode (legal because the left's guard holds
and the velocities agree), then the certified joint segment in that mode for the whole window,
then a switch into `A0`, whose guard is the whole envelope.

Standalone: the response is written here, not replayed from the tool's choice cover. The
hand-written general instance `Choice/General/VehicleHypercert.lean` replayed the emitted cover
until 2026-10-21, when its Theorem-3 part was retired (git 61d7389; only its Assumption 1 proof
remains); the generated bridge instance `InstancesV2/Bridge/VehicleHypercert.lean` replays the
cover now, its downward progress stage through `repoProgress_one_down`.
Existence of the right segment is the mirror argument (`hExistSegB_constMirror`), since a
constant field leaves the envelope from one of its edges and `WellFormedFlowB` does not hold.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.vehicle_hypercert
import RelCertifier.InstancesV2.Choice.ConstMirror

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceVehicleHypercert

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := vehicle_hypercert_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := vehicle_hypercert_IRv2.R.modes.getD q dm

abbrev mv : Var 2 := (Side.Aux, 0)
abbrev tg : Var 2 := (Side.Aux, 1)

noncomputable def fL (l : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domL : Formula (Var 2) := hostEvolve vs 2 Side.L (mL 0)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
noncomputable def env : Formula (Var 2) := Formula.and domL domR

/-- The declared invariant's components (row 0; every row is the same). -/
noncomputable def comps : List (Term (Var 2)) :=
  hostComps vs 2 (vehicle_hypercert_IRv2.invariants.getD 0 ("", PForm.tt)).2
noncomputable def g : Term (Var 2) := comps.getD 0 (Term.const 0)
noncomputable def gs : List (Term (Var 2)) := [comps.getD 1 (Term.const 0)]

noncomputable def cL (l : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.L (cutAtomsOfX vehicle_hypercert_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 2) :=
  cutPairsX vs 2 Side.R (cutAtomsOfX vehicle_hypercert_cutsV2X.R (mR q).name)

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp004 : Run.parseRat "0.04" = some ((1:ℚ)/25) := by
  have h : parseQ "0.04" = some (⟨4, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp058 : Run.parseRat "0.58" = some ((29:ℚ)/50) := by
  have h : parseQ "0.58" = some (⟨58, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp056 : Run.parseRat "0.56" = some ((14:ℚ)/25) := by
  have h : parseQ "0.56" = some (⟨56, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Evaluations of the lowered data -/

/-- The accelerations, by mode index. -/
noncomputable def acc : ℕ → ℝ
  | 0 => -1/25 | 1 => -1/50 | 2 => 0 | 3 => 1/50 | _ => 1/25

/-- The guard bounds, by mode index. -/
noncomputable def lo : ℕ → ℝ
  | 0 => 1/25 | 1 => 1/50 | _ => 0
noncomputable def hi : ℕ → ℝ
  | 0 => 3/5 | 1 => 3/5 | 2 => 3/5 | 3 => 29/50 | _ => 14/25

/-- The coordinate field: the acceleration on index 0, the padding index frozen. -/
noncomputable def cf (q : ℕ) : Fin 2 → ℝ := fun i => if i = 0 then acc q else 0

theorem fL_eval (l : ℕ) (hl : l < 5) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fL l i) x = cf l i := by
  fin_cases i <;> interval_cases l <;>
    simp [fL, hostDyn, mL, vehicle_hypercert_IRv2, vs, Run.dynOf, Run.lowerE, hp00, hp004,
      hp002, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Lv, cf, acc] <;> norm_num

theorem fR_eval (q : ℕ) (hq : q < 5) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fR q i) x = cf q i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mR, vehicle_hypercert_IRv2, vs, Run.dynOf, Run.lowerE, hp00, hp004,
      hp002, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cf, acc] <;> norm_num

theorem sat_domL (x : State (Var 2)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 3/5) := by
  simp only [domL, hostEvolve, mL, vehicle_hypercert_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp06, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  simp only [domR, hostEvolve, mR, vehicle_hypercert_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp06, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem domL_univ (l : ℕ) (hl : l < 5) : hostEvolve vs 2 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 5) : hostEvolve vs 2 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

theorem comps_eq : comps =
    [Term.binop .sub (Term.var (Lv 0)) (Term.var (Rv 0)),
     Term.binop .sub (Term.var (Rv 0)) (Term.var (Lv 0))] := by
  have hdL : ("L_v".drop 2).copy = "v" := by decide
  have hdR : ("R_v".drop 2).copy = "v" := by decide
  simp [comps, hostComps, vehicle_hypercert_IRv2, Oracle.invComponents, Run.lowerE, vs,
    Run.resolveVar, Parse.dr, hdL, hdR, List.findIdx?_cons, ITerm.toHost, Lv, Rv]

/-- Every invariant row is row 0. -/
theorem comps_row (l : ℕ) (hl : l < 5) :
    hostComps vs 2 (vehicle_hypercert_IRv2.invariants.getD l ("", PForm.tt)).2 = comps := by
  interval_cases l <;> rfl

theorem sat_FMgs (x : State (Var 2)) : Formula.sat (FM g gs) x ↔ x (Lv 0) = x (Rv 0) := by
  rw [sat_FM_iff]
  simp [g, gs, comps_eq, Term.eval, AOp.interp]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨le_of_eq h, ge_of_eq h⟩

/-! ## The cut families, concretely -/

/-- The kept cuts of mode `q` (the same on both sides), as a predicate on the velocity. -/
def cutP : ℕ → ℝ → Prop
  | 0, v => v ≤ 3/5
  | 1, v => v ≤ 3/5
  | 2, v => 0 ≤ v ∧ v ≤ 3/5
  | _, v => 0 ≤ v

theorem gL_le06 : hostAtomG vs 2 Side.L (.cmp "<=" (.var "v") (.num "0.6")) = thrLe (Lv 0) (3/5) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp06, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Lv]
theorem gL_ge0 : hostAtomG vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")) = thrGe (Lv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Lv]
theorem gR_le06 : hostAtomG vs 2 Side.R (.cmp "<=" (.var "v") (.num "0.6")) = thrLe (Rv 0) (3/5) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp06, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe, Rv]
theorem gR_ge0 : hostAtomG vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")) = thrGe (Rv 0) 0 := by
  simp [hostAtomG, cutAtomG, Run.lowerE, hp00, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe, Rv]

theorem cL_01 (l : ℕ) (hl : l = 0 ∨ l = 1) : cL l =
    [(hostAtomF vs 2 Side.L (.cmp "<=" (.var "v") (.num "0.6")), thrLe (Lv 0) (3/5))] := by
  rw [← gL_le06]; rcases hl with rfl | rfl <;> rfl
theorem cL_2 : cL 2 =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Lv 0) 0),
     (hostAtomF vs 2 Side.L (.cmp "<=" (.var "v") (.num "0.6")), thrLe (Lv 0) (3/5))] := by
  rw [← gL_ge0, ← gL_le06]; rfl
theorem cL_34 (l : ℕ) (hl : l = 3 ∨ l = 4) : cL l =
    [(hostAtomF vs 2 Side.L (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Lv 0) 0)] := by
  rw [← gL_ge0]; rcases hl with rfl | rfl <;> rfl
theorem cR_01 (q : ℕ) (hq : q = 0 ∨ q = 1) : cR q =
    [(hostAtomF vs 2 Side.R (.cmp "<=" (.var "v") (.num "0.6")), thrLe (Rv 0) (3/5))] := by
  rw [← gR_le06]; rcases hq with rfl | rfl <;> rfl
theorem cR_2 : cR 2 =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Rv 0) 0),
     (hostAtomF vs 2 Side.R (.cmp "<=" (.var "v") (.num "0.6")), thrLe (Rv 0) (3/5))] := by
  rw [← gR_ge0, ← gR_le06]; rfl
theorem cR_34 (q : ℕ) (hq : q = 3 ∨ q = 4) : cR q =
    [(hostAtomF vs 2 Side.R (.cmp ">=" (.var "v") (.num "0.0")), thrGe (Rv 0) 0)] := by
  rw [← gR_ge0]; rcases hq with rfl | rfl <;> rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 5) :
    ∀ x ∈ cutAtomsOfX vehicle_hypercert_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  interval_cases l <;>
    simp [cutAtomsOfX, vehicle_hypercert_cutsV2X, mL, vehicle_hypercert_IRv2] at hx <;>
    (try rcases hx with rfl | rfl) <;> (try subst hx) <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 5) :
    ∀ x ∈ cutAtomsOfX vehicle_hypercert_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  intro x hx
  interval_cases q <;>
    simp [cutAtomsOfX, vehicle_hypercert_cutsV2X, mR, vehicle_hypercert_IRv2] at hx <;>
    (try rcases hx with rfl | rfl) <;> (try subst hx) <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 5) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 5) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 2)) (hiff : AtomsIff cs) (ν : State (Var 2)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatL_val (l : ℕ) (hl : l < 5) (ν : State (Var 2)) :
    CutSat (cL l) ν ↔ cutP l (ν (Lv 0)) := by
  rw [cutSat_iff _ (hiffL l hl)]
  interval_cases l
  · rw [cL_01 0 (by simp)]; simp [cutP, thrLe, Term.eval, AOp.interp]
  · rw [cL_01 1 (by simp)]; simp [cutP, thrLe, Term.eval, AOp.interp]
  · rw [cL_2]; simp [cutP, thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cL_34 3 (by simp)]; simp [cutP, thrGe, Term.eval, AOp.interp]
  · rw [cL_34 4 (by simp)]; simp [cutP, thrGe, Term.eval, AOp.interp]

theorem cutSatR_val (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    CutSat (cR q) ν ↔ cutP q (ν (Rv 0)) := by
  rw [cutSat_iff _ (hiffR q hq)]
  interval_cases q
  · rw [cR_01 0 (by simp)]; simp [cutP, thrLe, Term.eval, AOp.interp]
  · rw [cR_01 1 (by simp)]; simp [cutP, thrLe, Term.eval, AOp.interp]
  · rw [cR_2]; simp [cutP, thrGe, thrLe, Term.eval, AOp.interp]
  · rw [cR_34 3 (by simp)]; simp [cutP, thrGe, Term.eval, AOp.interp]
  · rw [cR_34 4 (by simp)]; simp [cutP, thrGe, Term.eval, AOp.interp]

/-- The envelope implies every mode's kept cuts. -/
theorem cutP_of_env (q : ℕ) (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 3/5) : cutP q v := by
  match q with
  | 0 => exact h1
  | 1 => exact h1
  | 2 => exact ⟨h0, h1⟩
  | _ + 3 => exact h0

theorem sat_guardL (l : ℕ) (hl : l < 5) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.L (mL l)) ν ↔ (lo l ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ hi l) := by
  interval_cases l <;>
    simp [hostGuard, mL, vehicle_hypercert_IRv2, Run.lowerF, Run.lowerE, hp00, hp06, hp004,
      hp002, hp058, hp056, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Lv, lo, hi]

theorem sat_guardR (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ (lo q ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ hi q) := by
  interval_cases q <;>
    simp [hostGuard, mR, vehicle_hypercert_IRv2, Run.lowerF, Run.lowerE, hp00, hp06, hp004,
      hp002, hp058, hp056, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Rv, lo, hi]

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

theorem hfL (l : ℕ) (hl : l < 5) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, vehicle_hypercert_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 5) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, vehicle_hypercert_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, vehicle_hypercert_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, vehicle_hypercert_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 5) : (hostGuard vs 2 Side.L (mL l)).fv ⊆ range Lv :=
  fun x hx => side_eq_L_mem (hostForm_side (resolvesTo_L vs) (mL l).guard
    (by interval_cases l <;>
        simp [mL, vehicle_hypercert_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x hx)

theorem comps_fv : ∀ c ∈ g :: gs, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  simp only [g, gs, comps_eq, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · intro x hx
    simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp

theorem thr_fv_L (j : Fin 2) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 2) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 5) (hq : q < 5) :
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
      simp only [cL_01 0 (by simp), cL_01 1 (by simp), cL_2, cL_34 3 (by simp),
        cL_34 4 (by simp), List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      first | exact (thr_fv_L _ _).1 | exact (thr_fv_L _ _).2
  have hRa : ∀ a ∈ cR q, a.2.fv ⊆ range Lv ∪ range Rv := by
    intro a ha
    interval_cases q <;>
      simp only [cR_01 0 (by simp), cR_01 1 (by simp), cR_2, cR_34 3 (by simp),
        cR_34 4 (by simp), List.mem_cons, List.not_mem_nil, or_false] at ha <;>
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
  (List.range 5).flatMap (fun s => (List.range 5).map (fun t => (s, t)))

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range vehicle_hypercert_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (vehicle_hypercert_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

theorem edgeList_mem (s t : ℕ) (hs : s < 5) (ht : t < 5) : (s, t) ∈ edgeList := by
  simp [edgeList, hs, ht]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 5 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem hguardR (q : ℕ) (hq : q < 5) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R vs (mR q) (by
    interval_cases q <;>
      simp [mR, vehicle_hypercert_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 5 := by decide

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

theorem edge_mem (s t : ℕ) (hs : s < 5) (ht : t < 5) : edgeW s t ∈ Gr.edgesFrom s :=
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
  if q < 5 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem region_fv (q : ℕ) : (region q).fv ⊆ range Rv := by
  by_cases h5 : q < 5
  · simp only [region, h5, if_true]
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
      simp only [cR_01 0 (by simp), cR_01 1 (by simp), cR_2, cR_34 3 (by simp),
        cR_34 4 (by simp), List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      (try rcases ha with rfl | rfl) <;> (try subst ha) <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h5, if_false]
    simp [Formula.fv, Term.fv]

noncomputable def gregion (q : ℕ) : Formula (Var 2) :=
  regionG (fun q => hostGuard vs 2 Side.R (mR q)) region q

theorem hguardR_all (q : ℕ) : (hostGuard vs 2 Side.R (mR q)).fv ⊆ range Rv :=
  hostGuard_fv_R_getD vs _ dm rfl (by simp [vehicle_hypercert_IRv2, Parse.PForm.namesFree,
    Parse.PExpr.namesFree]) q

theorem gregion_fv (q : ℕ) : (gregion q).fv ⊆ range Rv :=
  regionG_fv_sub (hguardR_all q) (region_fv q)

/-! ## The certified pairings: each left mode with the same right mode, stretch 1 -/

noncomputable def lam (_l _q : ℕ) : ℝ := 1

theorem lam_pos (l q : ℕ) : 0 < lam l q := by unfold lam; norm_num

/-- O2: the kept atoms stay along the joint flow of a pairing `(l, l)` (constant fields
pointing inward at each kept threshold). -/
theorem stayL (l : ℕ) (hl : l < 5) :
    AtomsStayC (cL l) (jointSys (fL l) (fR l) (Term.const (lam l l)))
      (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hf : ∀ z, Term.eval (fL l 0) z = acc l := fun z => by rw [fL_eval l hl]; simp [cf]
  interval_cases l
  · rw [cL_01 0 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_L 0 (3/5) _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]; norm_num) hinit
  · rw [cL_01 1 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_L 0 (3/5) _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]; norm_num) hinit
  · rw [cL_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
    · exact boxle_thrLe_L 0 (3/5) _ _ _ _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cL_34 3 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cL_34 4 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_L 0 0 _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit

theorem stayR (l : ℕ) (hl : l < 5) :
    AtomsStayC (cR l) (jointSys (fL l) (fR l) (Term.const (lam l l)))
      (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR l hl a ha ν).mp (hν a ha)
  have hf : ∀ z, Term.eval (fR l 0) z = acc l := fun z => by rw [fR_eval l hl]; simp [cf]
  have hc := le_of_lt (lam_pos l l)
  interval_cases l
  · rw [cR_01 0 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_R 0 (3/5) _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]; norm_num) hinit
  · rw [cR_01 1 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrLe_R 0 (3/5) _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]; norm_num) hinit
  · rw [cR_2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
    · exact boxle_thrLe_R 0 (3/5) _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
        (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cR_34 3 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit
  · rw [cR_34 4 (by simp)] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact boxle_thrGe_R 0 0 _ _ _ hc _ (Formula.and domL domR) (fun x h => h)
      (fun z _ _ => by rw [hf]; simp [acc]) hinit

/-! ## Existence: the right copies the left (`hExistSegB_constMirror`) -/

theorem es (l : ℕ) (hl : l < 5) (dt : ℝ) (A : Formula (Var 2))
    (hA : ∀ σ, Formula.sat A σ → σ (Lv 0) = σ (Rv 0)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR l) (Term.const (lam l l)) domL domR dt
        (Function.update σ tg 0) := by
  intro σ hσ
  have heq := hA σ hσ.1
  refine hExistSegB_constMirror (fL l) (fR l) _ domL domR dt _ (cf l)
    (fL_eval l hl) (fR_eval l hl) (fun _ => by simp [Term.eval, lam]) ?_
  intro x y hxy hx
  have h0 := hxy 0
  have hνL : Function.update σ tg 0 (Lv 0) = σ (Lv 0) :=
    Function.update_of_ne (by simp [Lv, tg]) _ _
  have hνR : Function.update σ tg 0 (Rv 0) = σ (Rv 0) :=
    Function.update_of_ne (by simp [Rv, tg]) _ _
  rw [hνL, hνR] at h0
  rw [sat_domL] at hx
  rw [sat_domR]
  constructor <;> linarith [hx.1, hx.2]

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left mode `l`, right mode `l` (the chosen one), stretch 1, strata order
`[0, 1]`, the invariant row of `l`. -/
def Verd (l : ℕ) : Prop :=
  modalVerdX vehicle_hypercert_IRv2 vehicle_hypercert_cutsV2X 2 l [0, 1] (lam l l) l l

theorem verd_core (l : ℕ) (hl : l < 5) (h : Verd l) :
    VerdXCore (g :: gs) (fL l) (fR l) (lam l l)
      (domCutX (Formula.and domL domR) (cL l) (cR l)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  have hvs : vehicle_hypercert_IRv2.L.stateVars = vs := rfl
  simp only [hvs, comps_row l hl] at h'
  rw [← domL_univ l hl, ← domR_univ l hl]
  exact h'

/-! ## The coupling, the window response -/

theorem anchor_eq (l : ℕ) (σ : State (Var 2))
    (h : Formula.sat (FM g (gs ++ atomTerms (cL l) (cR l))) σ) : σ (Lv 0) = σ (Rv 0) :=
  (sat_FMgs σ).mp ((sat_FM_append g gs _ σ).mp h).1

theorem couple (l : ℕ) (hl : l < 5) (dt : ℝ) (hv : Verd l) :
    ∀ σ, Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ →
      faModalB (Equiv.refl (Var 2))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR l) (Term.const 1)) domR)
        (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l))) (Formula.and domL domR))
        tg dt (Function.update σ tg 0) :=
  couple_cutX g gs (g :: gs) (cL l) (cR l) (fL l) (fR l) (lam l l) (lam_pos l l) domL domR 1 dt
    (hfL l hl) (hfR l hl) hdomL hdomR (anchor_fv l l hl hl) (fun c hc => hc)
    (fun c hc => hc) (hiffL l hl) (hiffR l hl) (stayL l hl) (stayR l hl)
    (verd_core l hl hv) (es l hl dt _ (anchor_eq l))

theorem sat_faModal_monoPost {P Q : Program (Var 2)} {A B : Formula (Var 2)}
    (hAB : ∀ ν, Formula.sat A ν → Formula.sat B ν) {σ : State (Var 2)}
    (h : Formula.sat (faModal (Equiv.refl (Var 2)) P Q A) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2)) P Q B) σ := by
  rw [faModal_sat] at h ⊢
  intro ν hν
  obtain ⟨μ, hμ, hA⟩ := h ν hν
  exact ⟨μ, hμ, hAB μ hA⟩

theorem respond (l : ℕ) (hl : l < 5) (dt : ℝ) (hv : Verd l) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ) :
    Formula.sat (faModal (Equiv.refl (Var 2))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq (([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
        ++ [Program.ode (rightBlock (fR l) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM g gs) env) (region l))) σ := by
  have htgF : tg ∉ (FM g (gs ++ atomTerms (cL l) (cR l))).fv :=
    notMem_FM_fv (fun g' hg' hx => by
      rcases anchor_fv l l hl hl g' (by simpa using hg') hx with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact absurd hi (by simp [Lv, Prod.ext_iff])
      · exact absurd hi (by simp [Rv, Prod.ext_iff]))
  have htgenv : tg ∉ (Formula.and domL domR).fv := by
    rintro (h | h)
    · exact aux_notin_range_Lv 1 (hdomL h)
    · exact aux_notin_range_Rv 1 (hdomR h)
  have hfa := Hmulti_windowRF_prefixed (fL l) domL (FM g (gs ++ atomTerms (cL l) (cR l)))
    (Formula.and domL domR) 1 dt 1 htgF htgenv
    (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2)))
    (by intro h hh; simp at hh)
    (fun σ' hσ' => hσ'.2.1)
    (by intro h hh; simp at hh)
    (hfL l hl) hdomL
    [Program.ode (rightBlock (fR l) (Term.const 1)) domR] rfl (by norm_num)
    (by
      intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      rw [Program.rename_refl]
      exact hdisH_progR (⟨fR l, Term.const 1, domR⟩ : RepoHop 2)
        (hfR l hl) (by simp [Term.fv]) hdomR (hfL l hl) hdomL)
    (by
      intro Q hQ σ' hσ'
      rw [List.mem_singleton] at hQ
      subst hQ
      exact couple l hl dt hv σ' hσ')
    hσ
  rw [show (([] : List ℕ).map (fun p => (⟨fR p, Term.const 1, domR⟩ : RepoHop 2))).map
      (fun h => h.progR)
      = ([] : List ℕ).map (fun p => Program.ode (rightBlock (fR p) (Term.const 1)) domR)
    from rfl] at hfa
  refine sat_faModal_monoPost ?_ hfa
  intro ν hν
  obtain ⟨hFν, hatν⟩ := (sat_FM_append g gs _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR l hl) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt l hl ν).mpr hRν⟩

/-! ## The windows -/

noncomputable def leftData : List (Formula (Var 2) × (Fin 2 → Term (Var 2))
    × Formula (Var 2) × ℕ) :=
  (List.range 5).map (fun l => (hostGuard vs 2 Side.L (mL l), fL l, domL, 1))

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

/-- **Nonblocking**: at the end of any response the right is in the envelope, where `A0`'s
guard (the whole envelope) holds and `A0`'s kept cuts hold. -/
theorem nonblock (q : ℕ) (hq : q < 5) :
    NonblockingAt Gr q (Formula.and (Formula.and (FM g gs) env) (region q))
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) := by
  intro μ ⟨hFe, _⟩
  have hR := (sat_domR μ).mp hFe.2.2
  refine ⟨edgeW q 2, edge_mem q 2 hq (by norm_num), ?_, hFe, ?_⟩
  · exact (sat_guardR 2 (by norm_num) μ).mpr (by simp [lo, hi]; exact hR)
  · exact (sat_region_lt 2 (by norm_num) μ).mpr
      ((cutSatR_val 2 (by norm_num) μ).mpr (cutP_of_env 2 _ hR.1 hR.2))

/-- The response from an anchor of `(l, l)`: the certified joint segment in `l` for the whole
window, then a switch into `A0`. -/
theorem flowCase (l : ℕ) (hl : l < 5) (dt : ℝ) (hv : Verd l) {σ : State (Var 2)}
    (hanchor : Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
        (Formula.and domL domR)) σ) :
    GResp Gr l (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ :=
  gresp_final (Gr_modeAt l hl) (respond l hl dt hv hanchor) (nonblock l hl)

/-- The anchor of `(l, l)` holds at every loop state (the envelope implies every kept cut). -/
theorem anchor_of_loop (l : ℕ) (hl : l < 5) {σ : State (Var 2)}
    (hσ : Formula.sat (Formula.and (FM g gs) env) σ) :
    Formula.sat (Formula.and (FM g (gs ++ atomTerms (cL l) (cR l)))
      (Formula.and domL domR)) σ := by
  have hL0 := (sat_domL σ).mp hσ.2.1
  have hR0 := (sat_domR σ).mp hσ.2.2
  refine ⟨(sat_FM_append g gs _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
  exact (atomTerms_iff (hiffL l hl) (hiffR l hl) σ).mpr
    ⟨(cutSatL_val l hl σ).mpr (cutP_of_env l _ hL0.1 hL0.2),
     (cutSatR_val l hl σ).mpr (cutP_of_env l _ hR0.1 hR0.2)⟩

/-- **The chosen mode.** From any right start mode `q`, after the left run the right hops
into the left's mode `l` (its guard holds: it is the left's guard at the same velocity, and
the left run does not move the right), then responds from `l`. -/
theorem hopCase (l q : ℕ) (hl : l < 5) (hq : q < 5) (dt : ℝ) (hv : Verd l)
    {σ : State (Var 2)} (hσ : Formula.sat (Formula.and (FM g gs) env) σ) :
    GResp Gr q (gwindowSeg (hostGuard vs 2 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
      (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  refine gresp_gate (fun hguard => ?_)
  have hframesR := vars_windowSegL_sub (fL l) domL 1 dt 1 (hfL l hl) hdomL
  have heq := (sat_FMgs σ).mp hσ.1
  have hgR : Formula.sat (hostGuard vs 2 Side.R (mR l)) σ := by
    rw [sat_guardR l hl, ← heq]
    exact (sat_guardL l hl σ).mp hguard
  by_cases hql : q = l
  · subst hql
    exact flowCase q hl dt hv (anchor_of_loop q hl hσ)
  · refine gresp_hop (Gr_modeAt q hq) (edge_mem q l hq hl) ?_
      (flowCase l hl dt hv (anchor_of_loop l hl hσ))
    intro ν hrun
    exact ⟨frames_right hframesR hdomR hrun hσ.2.2, frames_right hframesR (hguardR l hl) hrun hgR⟩

theorem Hmulti (dt : ℝ) (hv : ∀ l < 5, Verd l) :
    ∀ P ∈ leftProgs dt, ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (FM g gs) env) σ →
      Formula.sat (hostGuard vs 2 Side.R (mR q)) σ → Formula.sat (region q) σ →
      GResp Gr q P (fun qf => Formula.and (Formula.and (FM g gs) env) (region qf)) σ := by
  intro P hP q hq σ _ hσ _ _
  rw [Gr_len] at hq
  simp only [leftProgs, leftData, List.map_map, List.mem_map, List.mem_range] at hP
  obtain ⟨l, hl, rfl⟩ := hP
  exact hopCase l q hl hq dt (hv l hl) hσ

/-! ## Theorem 3 -/

/-- **`vehicle_hypercert` (choice exhibit), modal Theorem 3 at the declared invariant
`v_L = v_R`.** Left: the five guard-gated windows; right: the five-mode guarded automaton of
the file (every edge testing the entered mode's lowered guard). The response chooses the
left's mode (a zero-duration hop when the right starts elsewhere), runs the certified joint
segment there, and switches into `A0`. Residuals: five stratified verdict packs, one per
diagonal pairing (`modalVerdX`, the tool's own queries). -/
theorem vehicle_hypercert_modal (dt : ℝ) (hv : ∀ l < 5, Verd l) :
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
          Hmulti dt hv P hP q hq σ hmv hσ hg hreg))
  · exact hddF_multiR_G Gr 0 1 dt leftData gregion (canonInvM g gs) domL domR
      (by decide) hgR hRv hL (fun q _ => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR

end ChoiceVehicleHypercert
end RelCertifier

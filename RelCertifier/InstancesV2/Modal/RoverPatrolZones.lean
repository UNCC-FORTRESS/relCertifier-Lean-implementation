/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) — mode-keyed Theorem 3 at the declared rows

The file declares one row per LEFT zone (`v_L ≤ v_R ∧ s_L ≤ s_R + m`, `m = 0.5` in `SLOW`,
`1` in `MEDIUM_ECO`/`MEDIUM_BRISK`, `2` in `FAST`). This leaf composes the per-left-mode modal
statements over the file's left automaton (`ModeHandoff.theorem3_modeKeyed`), with
`mv = (Aux, 0)`, the window clock `tg = (Aux, 1)` and the left mode variable `u_L = (Aux, 2)`
(lowered at `n = 3`: `vars = ["v", "s"]`, pad 2).

Adapted from `InstancesV2/Modal/PlatoonDelayLinkloss.lean` (the mode-keyed composition) and
`InstancesV2/Modal/ChargerFastTapers.lean` (the dynamic right-only reposition prefix,
`repoPrefixA`/`hopA`, re-stated here at `n = 3`). Every right driving mode is the affine loop
`v' = c − v`, `s' = v` (`c = 0.6, 0.9, 1.1, 1.5`); its run is the explicit solution
`v(t) = c + (v₀ − c) e^{−t}`, `s(t) = s₀ + c t + (v₀ − c)(1 − e^{−t})`, which stays in the
envelope `v ∈ [0, 1.6]`, `s ≥ 0` (the odometer has no upper wall: `docs/SUITE-REDESIGN.md`
§19). Responses, per left window and right start (the emitted cover): stay in a jointOK start
on the certified joint segment; from a start in an earlier zone (not jointOK) reposition
right-only in the start mode (and onward along the declared edges) until the odometer reaches
the target zone's floor, then the certified joint piece in the target zone. The pruned sink
`STALL` is excluded by its (false) region.
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.Cuts.rover_patrol_zones

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2RoverPatrolZones

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

def vs : List String := ["v", "s"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mL (l : ℕ) : PMode := rover_patrol_zones_IRv2.L.modes.getD l dm
def mR (q : ℕ) : PMode := rover_patrol_zones_IRv2.R.modes.getD q dm

abbrev mv : Var 3 := (Side.Aux, 0)
abbrev tg : Var 3 := (Side.Aux, 1)
abbrev uL : Var 3 := (Side.Aux, 2)

noncomputable def fL (l : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.L (mL l)
noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domL : Formula (Var 3) := hostEvolve vs 3 Side.L (mL 0)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
noncomputable def env : Formula (Var 3) := Formula.and domL domR

noncomputable def comps (l : ℕ) : List (Term (Var 3)) :=
  hostComps vs 3 (rover_patrol_zones_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def g (l : ℕ) : Term (Var 3) := (comps l).getD 0 (Term.const 0)
noncomputable def gs (l : ℕ) : List (Term (Var 3)) := [(comps l).getD 1 (Term.const 0)]

/-! ## Parse pins -/

theorem hp125 : Run.parseRat "1.25" = some ((5:ℚ)/4) := by
  have h : parseQ "1.25" = some (⟨125, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp048 : Run.parseRat "0.48" = some ((12:ℚ)/25) := by
  have h : parseQ "0.48" = some (⟨48, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp072 : Run.parseRat "0.72" = some ((18:ℚ)/25) := by
  have h : parseQ "0.72" = some (⟨72, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp088 : Run.parseRat "0.88" = some ((22:ℚ)/25) := by
  have h : parseQ "0.88" = some (⟨88, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp12 : Run.parseRat "1.2" = some ((6:ℚ)/5) := by
  have h : parseQ "1.2" = some (⟨12, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp09 : Run.parseRat "0.9" = some ((9:ℚ)/10) := by
  have h : parseQ "0.9" = some (⟨9, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp11 : Run.parseRat "1.1" = some ((11:ℚ)/10) := by
  have h : parseQ "1.1" = some (⟨11, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hpm20 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp16 : Run.parseRat "1.6" = some ((8:ℚ)/5) := by
  have h : parseQ "1.6" = some (⟨16, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp500 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp03 : Run.parseRat "0.3" = some ((3:ℚ)/10) := by
  have h : parseQ "0.3" = some (⟨3, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-! ## Per-zone constants (left and right zones share floors and caps) -/

/-- The zone floor on the odometer (`SLOW` 0, `MEDIUM_*` 20, `FAST` 50), as written. -/
def loS : ℕ → String
  | 0 => "0.0" | 1 => "20.0" | 2 => "20.0" | _ => "50.0"
def loQ : ℕ → ℚ
  | 0 => 0 | 1 => 20 | 2 => 20 | _ => 50
/-- The zone speed cap (`SLOW` 0.6, `MEDIUM_ECO` 0.9, `MEDIUM_BRISK` 1.1, `FAST` 1.5): the
guard's cap on both sides, and the right zone's command. -/
def capS : ℕ → String
  | 0 => "0.6" | 1 => "0.9" | 2 => "1.1" | _ => "1.5"
def capQ : ℕ → ℚ
  | 0 => 3/5 | 1 => 9/10 | 2 => 11/10 | _ => 3/2
/-- The deployed loop's set point `0.8 × command` (`0.48, 0.72, 0.88, 1.2`). -/
def cLQ : ℕ → ℚ
  | 0 => 12/25 | 1 => 18/25 | 2 => 22/25 | _ => 6/5
/-- The row's odometer margin (`0.5, 1, 1, 2`). -/
def mQ : ℕ → ℚ
  | 0 => 1/2 | 1 => 1 | 2 => 1 | _ => 2

noncomputable def loL (l : ℕ) : ℝ := (loQ l : ℝ)
noncomputable def capL (l : ℕ) : ℝ := (capQ l : ℝ)
noncomputable def cLv (l : ℕ) : ℝ := (cLQ l : ℝ)
noncomputable def mL' (l : ℕ) : ℝ := (mQ l : ℝ)

theorem hlo (l : ℕ) (hl : l < 4) : Run.parseRat (loS l) = some (loQ l) := by
  interval_cases l <;> simp only [loS, loQ] <;> first | exact hp00 | exact hp200 | exact hp500
theorem hcap (l : ℕ) (hl : l < 4) : Run.parseRat (capS l) = some (capQ l) := by
  interval_cases l <;> simp only [capS, capQ] <;>
    first | exact hp06 | exact hp09 | exact hp11 | exact hp15

theorem lo_nonneg (l : ℕ) (hl : l < 4) : 0 ≤ loL l := by
  interval_cases l <;> norm_num [loL, loQ]
theorem cap_bounds (l : ℕ) (hl : l < 4) : 3/5 ≤ capL l ∧ capL l ≤ 3/2 := by
  interval_cases l <;> norm_num [capL, capQ]
theorem cL_bounds (l : ℕ) (hl : l < 4) : 3/10 < cLv l ∧ cLv l < capL l := by
  interval_cases l <;> norm_num [cLv, cLQ, capL, capQ]

/-! ## Evaluations of the lowered data -/

theorem fL0_eval (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (fL l 0) x = 5/4 * (cLv l - x (Lv 0)) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp125, hp048,
      hp072, hp088, hp12, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv, cLv, cLQ]

theorem fL1_eval (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (fL l 1) x = x (Lv 0) := by
  interval_cases l <;>
    simp [fL, hostDyn, mL, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp125, hp048,
      hp072, hp088, hp12, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Lv]

/-- Right driving zones: `v' = c − v` with `c` the zone cap (= its command). -/
theorem fR0_eval (q : ℕ) (hq : q < 4) (x : State (Var 3)) :
    Term.eval (fR q 0) x = capL q - x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, capL, capQ]

theorem fR1_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 1) x = x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, rover_patrol_zones_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp09,
      hp11, hp15, hpm20, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domL (x : State (Var 3)) :
    Formula.sat domL x ↔ (0 ≤ x (Lv 0) ∧ x (Lv 0) ≤ 8/5 ∧ 0 ≤ x (Lv 1)) := by
  simp only [domL, hostEvolve, mL, rover_patrol_zones_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp16, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Lv, and_assoc]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 8/5 ∧ 0 ≤ x (Rv 1)) := by
  simp only [domR, hostEvolve, mR, rover_patrol_zones_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp16, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

theorem domL_univ (l : ℕ) (hl : l < 4) : hostEvolve vs 3 Side.L (mL l) = domL := by
  interval_cases l <;> rfl
theorem domR_univ (q : ℕ) (hq : q < 5) : hostEvolve vs 3 Side.R (mR q) = domR := by
  interval_cases q <;> rfl

/-- The declared rows, lowered: `v_L − v_R ≤ 0`, `s_L − (s_R + m) ≤ 0`. -/
theorem comps_eq (l : ℕ) (hl : l < 4) : comps l =
    [Term.binop .sub (Term.var (Lv 0)) (Term.var (Rv 0)),
     Term.binop .sub (Term.var (Lv 1)) (Term.binop .add (Term.var (Rv 1))
       (Term.const (mL' l)))] := by
  have h1 : ("L_v".drop 2).copy = "v" := by decide
  have h2 : ("R_v".drop 2).copy = "v" := by decide
  have h3 : ("L_s".drop 2).copy = "s" := by decide
  have h4 : ("R_s".drop 2).copy = "s" := by decide
  interval_cases l <;>
    simp [comps, hostComps, rover_patrol_zones_IRv2, Oracle.invComponents, Run.lowerE, vs,
      Run.resolveVar, Parse.dr, h1, h2, h3, h4, List.findIdx?_cons, hp05, hp10, hp20,
      ITerm.toHost, Lv, Rv, mL', mQ]

theorem comps_nil (l : ℕ) (hl : ¬ l < 4) : comps l = [] := by
  have : rover_patrol_zones_IRv2.invariants.getD l ("", PForm.tt) = ("", PForm.tt) :=
    List.getD_eq_default _ _ (by simp [rover_patrol_zones_IRv2]; omega)
  rw [comps, this]; simp [hostComps, Oracle.invComponents]

theorem eval_g (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval (g l) x = x (Lv 0) - x (Rv 0) := by
  simp [g, comps_eq l hl, Term.eval, AOp.interp]
theorem eval_gs0 (l : ℕ) (hl : l < 4) (x : State (Var 3)) :
    Term.eval ((gs l).getD 0 (Term.const 0)) x = x (Lv 1) - (x (Rv 1) + mL' l) := by
  simp [gs, comps_eq l hl, Term.eval, AOp.interp]

theorem comps_fv_all (l : ℕ) : ∀ c ∈ g l :: gs l, c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  by_cases hl : l < 4
  · simp only [g, gs, comps_eq l hl, List.getD_cons_zero, List.getD_cons_succ, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · intro x hx
      simp only [Term.fv, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp
  · simp only [g, gs, comps_nil l hl, List.getD_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at hc
    subst hc
    simp [Term.fv]

/-- The window's row is the left mode's own declared row (by name, as the tool reads it). -/
theorem invRow_faithful (l : ℕ) (hl : l < 4) :
    Handoff.invRowOf rover_patrol_zones_IRv2 (mL l)
      = some (rover_patrol_zones_IRv2.invariants.getD l ("", PForm.tt)).2 := by
  interval_cases l <;> decide

/-! ## The cut families -/

noncomputable def cL (l : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.L (cutAtomsOfX rover_patrol_zones_cutsV2X.L (mL l).name)
noncomputable def cR (q : ℕ) : List (CutAtomP 3) :=
  cutPairsX vs 3 Side.R (cutAtomsOfX rover_patrol_zones_cutsV2X.R (mR q).name)

theorem gs_ge (sd : Side) (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 sd (.cmp ">=" (.var "s") (.num s)) = thrGe ((sd, (1 : Fin 3)) : Var 3) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe]
theorem gv_ge (sd : Side) (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 sd (.cmp ">=" (.var "v") (.num s)) = thrGe ((sd, (0 : Fin 3)) : Var 3) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrGe]
theorem gv_le (sd : Side) (s : String) (K : ℚ) (h : Run.parseRat s = some K) :
    hostAtomG vs 3 sd (.cmp "<=" (.var "v") (.num s)) = thrLe ((sd, (0 : Fin 3)) : Var 3) (K : ℝ) := by
  simp [hostAtomG, cutAtomG, Run.lowerE, h, vs, Run.resolveVar, List.findIdx?_cons,
    ITerm.toHost, thrLe]

/-- A zone's three kept atoms on side `sd` (floor on `s`, the 0.3 m/s floor, the cap). -/
noncomputable def zoneAtoms (sd : Side) (l : ℕ) : List (CutAtomP 3) :=
  [(hostAtomF vs 3 sd (.cmp ">=" (.var "s") (.num (loS l))), thrGe ((sd, (1 : Fin 3)) : Var 3) (loL l)),
   (hostAtomF vs 3 sd (.cmp ">=" (.var "v") (.num "0.3")), thrGe ((sd, (0 : Fin 3)) : Var 3) (3/10)),
   (hostAtomF vs 3 sd (.cmp "<=" (.var "v") (.num (capS l))), thrLe ((sd, (0 : Fin 3)) : Var 3) (capL l))]

theorem zoneAtoms_eq (sd : Side) (l : ℕ) (hl : l < 4) : zoneAtoms sd l =
    [(hostAtomF vs 3 sd (.cmp ">=" (.var "s") (.num (loS l))),
        hostAtomG vs 3 sd (.cmp ">=" (.var "s") (.num (loS l)))),
     (hostAtomF vs 3 sd (.cmp ">=" (.var "v") (.num "0.3")),
        hostAtomG vs 3 sd (.cmp ">=" (.var "v") (.num "0.3"))),
     (hostAtomF vs 3 sd (.cmp "<=" (.var "v") (.num (capS l))),
        hostAtomG vs 3 sd (.cmp "<=" (.var "v") (.num (capS l))))] := by
  rw [gs_ge sd _ _ (hlo l hl), gv_ge sd _ _ hp03, gv_le sd _ _ (hcap l hl)]
  simp [zoneAtoms, loL, capL]

theorem cL_eq (l : ℕ) (hl : l < 4) : cL l = zoneAtoms Side.L l := by
  rw [zoneAtoms_eq Side.L l hl]
  interval_cases l <;> rfl
theorem cR_eq (q : ℕ) (hq : q < 4) : cR q = zoneAtoms Side.R q := by
  rw [zoneAtoms_eq Side.R q hq]
  interval_cases q <;> rfl

theorem atomsNonstrictL (l : ℕ) (hl : l < 4) :
    ∀ x ∈ cutAtomsOfX rover_patrol_zones_cutsV2X.L (mL l).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases l <;>
  · intro x hx
    simp [cutAtomsOfX, rover_patrol_zones_cutsV2X, mL, rover_patrol_zones_IRv2] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem atomsNonstrictR (q : ℕ) (hq : q < 4) :
    ∀ x ∈ cutAtomsOfX rover_patrol_zones_cutsV2X.R (mR q).name,
      ∃ op e1 e2, x.atom = PForm.cmp op e1 e2 ∧ (op = "<=" ∨ op = ">=") := by
  interval_cases q <;>
  · intro x hx
    simp [cutAtomsOfX, rover_patrol_zones_cutsV2X, mR, rover_patrol_zones_IRv2] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl, by simp⟩

theorem hiffL (l : ℕ) (hl : l < 4) : AtomsIff (cL l) :=
  atomsIff_cutPairsX (atomsNonstrictL l hl)
theorem hiffR (q : ℕ) (hq : q < 4) : AtomsIff (cR q) :=
  atomsIff_cutPairsX (atomsNonstrictR q hq)

theorem cutSat_iff (cs : List (CutAtomP 3)) (hiff : AtomsIff cs) (ν : State (Var 3)) :
    CutSat cs ν ↔ ∀ a ∈ cs, Term.eval a.2 ν ≤ 0 :=
  ⟨fun h a ha => (hiff a ha ν).mp (h a ha), fun h a ha => (hiff a ha ν).mpr (h a ha)⟩

theorem cutSatL_val (l : ℕ) (hl : l < 4) (ν : State (Var 3)) : CutSat (cL l) ν ↔
    (loL l ≤ ν (Lv 1) ∧ 3/10 ≤ ν (Lv 0) ∧ ν (Lv 0) ≤ capL l) := by
  rw [cutSat_iff _ (hiffL l hl), cL_eq l hl]
  simp [zoneAtoms, thrGe, thrLe, Term.eval, AOp.interp, Lv]

theorem cutSatR_val (q : ℕ) (hq : q < 4) (ν : State (Var 3)) : CutSat (cR q) ν ↔
    (loL q ≤ ν (Rv 1) ∧ 3/10 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ capL q) := by
  rw [cutSat_iff _ (hiffR q hq), cR_eq q hq]
  simp [zoneAtoms, thrGe, thrLe, Term.eval, AOp.interp, Rv]

/-! ## O1: the left guard implies the left atoms (the extended certificate, kernel-checked) -/

theorem hO1L (l : ℕ) (hl : l < 4) :
    ∀ ν, Formula.sat (hostGuard vs 3 Side.L (mL l)) ν → CutSat (cL l) ν := by
  intro ν hν
  refine cutSatL_of_guard rover_patrol_zones_cutsV2X_wf (mL l) ?_ ?_ ?_ ?_ ν hν
  · interval_cases l <;> rfl
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_patrol_zones_cutsV2X, mL, rover_patrol_zones_IRv2] at hx
      rcases hx with rfl | rfl | rfl <;> simp
  · interval_cases l <;>
    · intro x hx
      simp [cutAtomsOfX, rover_patrol_zones_cutsV2X, mL, rover_patrol_zones_IRv2] at hx
      rcases hx with rfl | rfl | rfl <;>
        simp [Run.lowerF, Run.lowerE, hp00, hp200, hp500, hp03, hp06, hp09, hp11, hp15, vs,
          Run.resolveVar, List.findIdx?_cons]
  · interval_cases l <;>
      simp [mL, rover_patrol_zones_IRv2, Run.lowerF, Run.lowerE, hp00, hp200, hp500, hp03, hp06,
        hp09, hp11, hp15, vs, Run.resolveVar, List.findIdx?_cons]

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

theorem hfL (l : ℕ) (hl : l < 4) : ∀ i, (fL l i).fv ⊆ range Lv := fun i x hx =>
  side_eq_L_mem (field_pipeline_side (resolvesTo_L vs) (some (mL l))
    (by interval_cases l <;> simp [mL, rover_patrol_zones_IRv2, Parse.PExpr.namesFree]) i x
    (fL_pipe l i ▸ hx))
theorem hfR (q : ℕ) (hq : q < 5) : ∀ i, (fR q i).fv ⊆ range Rv := fun i x hx =>
  side_eq_R_mem (field_pipeline_side (resolvesTo_R vs) (some (mR q))
    (by interval_cases q <;> simp [mR, rover_patrol_zones_IRv2, Parse.PExpr.namesFree]) i x
    (fR_pipe q i ▸ hx))
theorem hdomL : domL.fv ⊆ range Lv := fun x hx =>
  side_eq_L_mem (form_pipeline_side (resolvesTo_L vs) (some (mL 0))
    (by simp [mL, rover_patrol_zones_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domL_pipe ▸ hx))
theorem hdomR : domR.fv ⊆ range Rv := fun x hx =>
  side_eq_R_mem (form_pipeline_side (resolvesTo_R vs) (some (mR 0))
    (by simp [mR, rover_patrol_zones_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]) x
    (domR_pipe ▸ hx))
theorem hguardL (l : ℕ) (hl : l < 4) : (hostGuard vs 3 Side.L (mL l)).fv ⊆ range Lv := by
  refine hostGuard_fv_L vs (mL l) ?_
  interval_cases l <;>
    simp [mL, rover_patrol_zones_IRv2, Parse.PForm.namesFree, Parse.PExpr.namesFree]

theorem thr_fv_L (j : Fin 3) (K : ℝ) : (thrGe (Lv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Lv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp
theorem thr_fv_R (j : Fin 3) (K : ℝ) : (thrGe (Rv j) K).fv ⊆ range Lv ∪ range Rv ∧
    (thrLe (Rv j) K).fv ⊆ range Lv ∪ range Rv := by
  constructor <;> intro x hx <;> simp [thrGe, thrLe, Term.fv] at hx <;> subst hx <;> simp

theorem anchor_fv (l q : ℕ) (hl : l < 4) (hq : q < 4) :
    ∀ c ∈ g l :: gs l ++ atomTerms (cL l) (cR q), c.fv ⊆ range Lv ∪ range Rv := by
  intro c hc
  rw [List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact comps_fv_all l _ List.mem_cons_self
  rcases List.mem_append.mp hc with hc | hc
  · exact comps_fv_all l _ (List.mem_cons_of_mem _ hc)
  simp only [atomTerms, cL_eq l hl, cR_eq q hq, zoneAtoms, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (thr_fv_L 1 _).1
  · exact (thr_fv_L 0 _).1
  · exact (thr_fv_L 0 _).2
  · exact (thr_fv_R 1 _).1
  · exact (thr_fv_R 0 _).1
  · exact (thr_fv_R 0 _).2

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := Formula.tt, pruned := false }

/-- The declared transitions, as indices (`SLOW` 0, `MEDIUM_ECO` 1, `MEDIUM_BRISK` 2,
`FAST` 3, `STALL` 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 0), (0, 4), (1, 3), (1, 1), (1, 4), (2, 3), (2, 2), (2, 4), (3, 3),
   (3, 4), (4, 4)]

/-- **Faithfulness of the graph**: `edgeList` IS the file's `next` lists, resolved by name. -/
theorem edgeList_eq_IR : edgeList =
    (List.range rover_patrol_zones_IRv2.R.modes.length).flatMap (fun q =>
      (mR q).next.map (fun nm =>
        (q, (rover_patrol_zones_IRv2.R.modes.findIdx (·.name == nm))))) := by
  decide

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 5 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
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

/-! ## Regions: the right zone's kept cut atoms; the pruned sink `STALL` is excluded -/

noncomputable def region (q : ℕ) : Formula (Var 3) :=
  if q < 4 then cutF (cR q) else Formula.cmp CompOp.lt (Term.const 1) (Term.const 0)

theorem sat_region_lt (q : ℕ) (hq : q < 4) (ν : State (Var 3)) :
    Formula.sat (region q) ν ↔ CutSat (cR q) ν := by
  simp only [region, hq, if_true, sat_cutF]

theorem not_sat_region_sink (q : ℕ) (hq : ¬ q < 4) (ν : State (Var 3)) :
    ¬ Formula.sat (region q) ν := by
  simp [region, hq, Formula.sat, CompOp.interp, Term.eval]

theorem region_fv (q : ℕ) (_hq : q < 5) : (region q).fv ⊆ range Rv := by
  by_cases h4 : q < 4
  · simp only [region, h4, if_true]
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
    rw [cR_eq q h4] at ha
    simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      exact side_eq_R_mem (by
        simp only at hy
        unfold hostAtomF at hy
        exact hostForm_side (resolvesTo_R vs) _
          (by simp [Parse.PForm.namesFree, Parse.PExpr.namesFree]) y hy)
  · simp only [region, h4, if_false]
    simp [Formula.fv, Term.fv]

/-! ## O2: the kept atoms stay along the joint flows (rational, from the own field's sign) -/

theorem stayL (l q : ℕ) (hl : l < 4) :
    AtomsStayC (cL l) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffL l hl a ha ν).mp (hν a ha)
  have hc := cL_bounds l hl
  rw [cL_eq l hl] at ha
  simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact boxle_thrGe_L 1 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z hz _ => by rw [fL1_eval l hl]; exact ((sat_domL z).mp hz.1).1) hinit
  · exact boxle_thrGe_L 0 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fL0_eval l hl]; nlinarith) hinit
  · exact boxle_thrLe_L 0 _ _ _ _ _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fL0_eval l hl]; nlinarith) hinit

theorem stayR (l q : ℕ) (hq : q < 4) :
    AtomsStayC (cR q) (jointSys (fL l) (fR q) (Term.const 1)) (Formula.and domL domR) := by
  intro a ha ν hν
  have hinit := (hiffR q hq a ha ν).mp (hν a ha)
  have hc := cap_bounds q hq
  have h1 : (0:ℝ) ≤ 1 := zero_le_one
  rw [cR_eq q hq] at ha
  simp only [zoneAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact boxle_thrGe_R 1 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z hz _ => by rw [fR1_eval q (by omega)]; exact ((sat_domR z).mp hz.2).1) hinit
  · exact boxle_thrGe_R 0 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit
  · exact boxle_thrLe_R 0 _ _ _ _ h1 _ (Formula.and domL domR) (fun x h => h)
      (fun z _ hz => by rw [fR0_eval q hq]; linarith) hinit

/-! ## Existence: each driving zone's flow, explicitly

`v(t) = c + (v₀ − c) e^{−t}` (a convex combination of `v₀` and the command `c`, so inside
`[0, 1.6]`), `s(t) = s₀ + c t + (v₀ − c)(1 − e^{−t}) = s₀ + v₀ (1 − e^{−t}) + c (t − 1 + e^{−t})
≥ s₀` (the odometer never decreases; it has no upper wall). -/

noncomputable def ex (t : ℝ) : ℝ := Real.exp (-t)

noncomputable def solR (c : ℝ) (b : State (Var 3)) (t : ℝ) : State (Var 3) := fun x =>
  if x = Rv 0 then c + (b (Rv 0) - c) * ex t
  else if x = Rv 1 then b (Rv 1) + c * t + (b (Rv 0) - c) * (1 - ex t)
  else b x

theorem solR_0 (c : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c b t (Rv 0) = c + (b (Rv 0) - c) * ex t := by simp [solR]
theorem solR_1 (c : ℝ) (b : State (Var 3)) (t : ℝ) :
    solR c b t (Rv 1) = b (Rv 1) + c * t + (b (Rv 0) - c) * (1 - ex t) := by
  simp [solR, Rv, Prod.ext_iff]
theorem solR_other (c : ℝ) (b : State (Var 3)) (t : ℝ) {x : Var 3} (h0 : x ≠ Rv 0)
    (h1 : x ≠ Rv 1) : solR c b t x = b x := by
  simp [solR, h0, h1]

theorem ex_hasDeriv (t : ℝ) : HasDerivAt ex (-ex t) t := by
  have h := ((hasDerivAt_id t).neg).exp
  have h' : HasDerivAt ex (Real.exp (-id t) * (-1)) t := h
  refine h'.congr_deriv ?_
  simp only [ex, id]; ring
theorem ex_zero : ex 0 = 1 := by simp [ex]
theorem ex_pos (t : ℝ) : 0 < ex t := Real.exp_pos _
theorem ex_le_one {t : ℝ} (ht : 0 ≤ t) : ex t ≤ 1 := by
  unfold ex; rw [Real.exp_le_one_iff]; linarith
theorem ex_ge (t : ℝ) : 1 - t ≤ ex t := by
  unfold ex; have := Real.add_one_le_exp (-t); linarith

theorem solR_stays (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : Formula.sat domR b)
    {t : ℝ} (ht : 0 ≤ t) : Formula.sat domR (solR (capL q) b t) := by
  rw [sat_domR] at hb ⊢
  obtain ⟨h0, h1, h2⟩ := hb
  have hc := cap_bounds q hq
  have he0 := ex_pos t
  have he1 := ex_le_one ht
  have he2 := ex_ge t
  rw [solR_0, solR_1]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem rightBlock_bound_mem (q : ℕ) (i : Fin 3) :
    Rv i ∈ (rightBlock (fR q) (Term.const 1)).bound := by
  simp only [rightBlock, ODESystem.bound, List.map_map]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- **The explicit run of a driving zone** (any duration `s ≥ 0`, from any envelope state). -/
theorem flowR_run (q : ℕ) (hq : q < 4) (b : State (Var 3)) (hb : Formula.sat domR b)
    (s : ℝ) :
    solR (capL q) b 0 = b ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock (fR q) (Term.const 1),
          HasDerivWithinAt (fun u => solR (capL q) b u p.1) (p.2.eval (solR (capL q) b t))
            (Icc 0 s) t) ∧
      (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock (fR q) (Term.const 1)).bound →
        solR (capL q) b t x = b x) ∧
      (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (solR (capL q) b t)) := by
  set c := capL q with hcdef
  refine ⟨?_, ?_, ?_, fun t ht => solR_stays q hq b hb ht.1⟩
  · funext x
    by_cases h0 : x = Rv 0
    · subst h0; rw [solR_0, ex_zero]; ring
    by_cases h1 : x = Rv 1
    · subst h1; rw [solR_1, ex_zero]; ring
    exact solR_other c b 0 h0 h1
  · intro t ht p hp
    simp only [rightBlock, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hd := ex_hasDeriv t
    fin_cases i
    · have h := (((hd.const_mul (b (Rv 0) - c)).const_add c)).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c b u (Rv 0)) = fun u => c + (b (Rv 0) - c) * ex u := by
        funext u; exact solR_0 c b u
      show HasDerivWithinAt (fun u => solR c b u (Rv 0))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) (solR c b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR0_eval q hq, solR_0]
      exact h.congr_deriv (by rw [← hcdef]; ring)
    · have h := ((((hasDerivAt_id t).const_mul c).const_add (b (Rv 1))).add
        ((hd.const_sub 1).const_mul (b (Rv 0) - c))).hasDerivWithinAt (s := Icc 0 s)
      have hf : (fun u => solR c b u (Rv 1)) =
          fun u => (b (Rv 1) + c * id u) + (b (Rv 0) - c) * (1 - ex u) := by
        funext u; rw [solR_1]; rfl
      show HasDerivWithinAt (fun u => solR c b u (Rv 1))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) (solR c b t)) (Icc 0 s) t
      rw [hf]
      simp only [Term.eval, AOp.interp]
      rw [fR1_eval q (by omega), solR_0]
      exact h.congr_deriv (by ring)
    · have hcurve : (fun u => solR c b u (Rv 2)) = fun _ => b (Rv 2) := by
        funext u
        exact solR_other c b u (by simp [Rv, Prod.ext_iff]) (by simp [Rv, Prod.ext_iff])
      show HasDerivWithinAt (fun u => solR c b u (Rv 2))
        (Term.eval (Term.binop .mul (Term.const 1) (fR q 2)) (solR c b t)) (Icc 0 s) t
      rw [hcurve]
      simp only [Term.eval, AOp.interp]
      rw [fR2_eval q (by omega), mul_zero]
      exact hasDerivWithinAt_const t _ _
  · intro t _ x hx
    refine solR_other c b t (fun h => hx ?_) (fun h => hx ?_)
    · rw [h]; exact rightBlock_bound_mem q 0
    · rw [h]; exact rightBlock_bound_mem q 1

/-- A driving zone's program runs from `ω` to `solR c ω τ` for any `τ ≥ 0`. -/
theorem mode_run (q : ℕ) (hq : q < 4) (ω : State (Var 3)) (τ : ℝ) (hτ : 0 ≤ τ)
    (hb : Formula.sat domR ω) :
    Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) ω
      (solR (capL q) ω τ) := by
  obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q hq ω hb τ
  exact ⟨τ, solR (capL q) ω, hτ, h0, rfl, hder, hmask, hdom⟩

/-- **Reaching an odometer level.** In a driving zone `q`, from an envelope state with
`0.3 ≤ v₀ ≤ c_q`, the zone's program reaches `s_R = max(s₀, T)`; the speed only grows and
stays `≤ c_q`; the left (and Aux) coordinates are unchanged. Zero duration if `s₀ ≥ T`, else
the explicit run up to the crossing time (intermediate values: `s(t) ≥ s₀ + v₀ t`). -/
theorem mode_reach (q : ℕ) (hq : q < 4) (T : ℝ) (ω : State (Var 3))
    (hb : Formula.sat domR ω) (hv0 : 3/10 ≤ ω (Rv 0)) (hv1 : ω (Rv 0) ≤ capL q) :
    ∃ ρ, Program.sem (Program.ode (rightBlock (fR q) (Term.const 1)) domR) ω ρ ∧
      ρ (Rv 1) = max (ω (Rv 1)) T ∧ ω (Rv 0) ≤ ρ (Rv 0) ∧ ρ (Rv 0) ≤ capL q ∧
      ∀ x, (x ≠ Rv 0 ∧ x ≠ Rv 1) → ρ x = ω x := by
  by_cases hT : T ≤ ω (Rv 1)
  · obtain ⟨ρ, hsem, hρ⟩ := static_hop_existsR (fR := fR q) (lam := Term.const 1)
      (domR := domR) hb
    rw [hρ] at hsem
    exact ⟨ω, hsem, (max_eq_left hT).symm, le_refl _, hv1, fun _ _ => rfl⟩
  · replace hT : ω (Rv 1) < T := not_le.mp hT
    set c := capL q with hcdef
    set f : ℝ → ℝ := fun t => ω (Rv 1) + c * t + (ω (Rv 0) - c) * (1 - Real.exp (-t)) with hfdef
    have hcont : ContinuousOn f (Icc 0 ((T - ω (Rv 1)) / (3/10))) := by
      apply Continuous.continuousOn
      simp only [hfdef]
      fun_prop
    have hTm : 0 ≤ (T - ω (Rv 1)) / (3/10) := div_nonneg (by linarith) (by norm_num)
    have hf0 : f 0 = ω (Rv 1) := by simp [hfdef]
    have hlow : ∀ t, 0 ≤ t → ω (Rv 1) + ω (Rv 0) * t ≤ f t := by
      intro t ht
      have he := ex_ge t
      have : f t - (ω (Rv 1) + ω (Rv 0) * t) = (c - ω (Rv 0)) * (t - 1 + Real.exp (-t)) := by
        simp only [hfdef]; ring
      have h2 : 0 ≤ (c - ω (Rv 0)) * (t - 1 + Real.exp (-t)) := by
        apply mul_nonneg (by linarith)
        unfold ex at he; linarith
      linarith
    have hfT : T ≤ f ((T - ω (Rv 1)) / (3/10)) := by
      have := hlow _ hTm
      have h3 : (3/10) * ((T - ω (Rv 1)) / (3/10)) ≤ ω (Rv 0) * ((T - ω (Rv 1)) / (3/10)) :=
        mul_le_mul_of_nonneg_right hv0 hTm
      have h4 : (3/10) * ((T - ω (Rv 1)) / (3/10)) = T - ω (Rv 1) := by field_simp
      linarith
    obtain ⟨τ, hτI, hτf⟩ := intermediate_value_Icc hTm hcont ⟨by rw [hf0]; exact le_of_lt hT, hfT⟩
    refine ⟨_, mode_run q hq ω τ hτI.1 hb, ?_, ?_, ?_, ?_⟩
    · rw [solR_1, max_eq_right (le_of_lt hT), ← hτf]
      simp only [hfdef, ex, hcdef]
    · rw [solR_0]
      have := ex_le_one hτI.1
      have := ex_pos τ
      nlinarith
    · rw [solR_0]
      have := ex_pos τ
      nlinarith
    · intro x hx
      exact solR_other c ω τ hx.1 hx.2

/-- **Within-segment existence** (λ = 1): the left run masks the right coordinates, so the right
start of the stretched segment is the anchor's right state, in the envelope. -/
theorem es (l q : ℕ) (hq : q < 4) (dt : ℝ) (A : Formula (Var 3)) :
    ∀ σ, Formula.sat (Formula.and A (Formula.and domL domR)) σ →
      HExistSegB (fL l) (fR q) (Term.const 1) domL domR dt (Function.update σ tg 0) := by
  intro σ hσ s ΦL hs0 _ _ _ hmaskL _
  have hagree : ∀ i, ΦL s (Rv i) = σ (Rv i) := by
    intro i
    rw [hmaskL s (right_mem_Icc.mpr hs0) (Rv i) (fun hb => by
      obtain ⟨j, hj⟩ := leftBlock_bound_sub (fL l) _ hb
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff]))]
    exact Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _
  have hdom' : Formula.sat domR (ΦL s) := by
    refine (Formula.coincidence domR (fun x hx => ?_)).mp hσ.2.2
    obtain ⟨i, rfl⟩ := hdomR hx
    exact (hagree i).symm
  obtain ⟨h0, hder, hmask, hdom⟩ := flowR_run q hq (ΦL s) hdom' s
  exact ⟨solR (capL q) (ΦL s), h0, hder, hmask, hdom⟩

/-! ## The verdict packs (the tool's narrowed queries, read off the IR and certificate) -/

/-- One pack: left window `l` at its OWN declared row (`invRow = l`), right zone `q`, at the
cover's λ = 1 and strata order `[0, 1]`. -/
def Verd (l q : ℕ) : Prop :=
  modalVerdX rover_patrol_zones_IRv2 rover_patrol_zones_cutsV2X 3 l [0, 1] 1 l q

theorem verd_core (l q : ℕ) (hl : l < 4) (hq : q < 5) (h : Verd l q) :
    VerdXCore (g l :: gs l) (fL l) (fR q) 1
      (domCutX (Formula.and domL domR) (cL l) (cR q)) := by
  have h' := h
  unfold Verd modalVerdX at h'
  rw [← domL_univ l hl, ← domR_univ q hq]
  exact h'

/-! ## The coupling, the window response -/

/-- The joint-piece anchor of the pair `(l, q)`: row `l`, both zones' atoms, the envelope. -/
noncomputable def anchor (l q : ℕ) : Formula (Var 3) :=
  Formula.and (FM (g l) (gs l ++ atomTerms (cL l) (cR q))) (Formula.and domL domR)

theorem couple (l q : ℕ) (hl : l < 4) (hq : q < 4) (dt : ℝ) (hv : Verd l q) :
    ∀ σ, Formula.sat (anchor l q) σ →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q) (Term.const 1)) domR)
        (anchor l q) tg dt (Function.update σ tg 0) :=
  couple_cutX (g l) (gs l) (g l :: gs l) (cL l) (cR q) (fL l) (fR q) 1 one_pos domL domR 1 dt
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

theorem anchor_post (l q : ℕ) (hl : l < 4) (hq : q < 4) (ν : State (Var 3))
    (hν : Formula.sat (anchor l q) ν) :
    Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) ν := by
  obtain ⟨hFν, hatν⟩ := (sat_FM_append (g l) (gs l) _ ν).mp hν.1
  obtain ⟨-, hRν⟩ := (atomTerms_iff (hiffL l hl) (hiffR q hq) ν).mp hatν
  exact ⟨⟨hFν, hν.2⟩, (sat_region_lt q hq ν).mpr hRν⟩

theorem respond (l qs : ℕ) (hl : l < 4) (hqs : qs < 4) (dt : ℝ) (hv : Verd l qs)
    {σ : State (Var 3)} (hσ : Formula.sat (anchor l qs) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (windowSeg (leftBlock (fL l)) domL tg dt 1)
      (bigSeq ([] ++ [Program.ode (rightBlock (fR qs) (Term.const 1)) domR]))
      (Formula.and (Formula.and (FM (g l) (gs l)) env) (region qs))) σ := by
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
    (Formula.and domL domR) 1 dt 1 htgF htgenv [] (by simp)
    (fun σ' hσ' => hσ'.2.1) (by simp)
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
  refine sat_faModal_monoPost (A := anchor l qs) (anchor_post l qs hl hqs) ?_
  simpa [anchor] using hfa

/-! ## A right-only prefix hop whose landing predicate is arbitrary (from
`ChargerFastTapers.repoPrefixA` / `hopA` / `window1_of_B`, re-stated at `n = 3`) -/

theorem repoPrefixA {fL' fRh : Fin 3 → Term (Var 3)} {lamh : Term (Var 3)}
    {domL' domRh : Formula (Var 3)} {φ : Formula (Var 3)} {Q : Program (Var 3)}
    {dt : ℝ} {ω₀ : State (Var 3)}
    (hfL : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL : domL'.fv ⊆ range Lv)
    (hfR : ∀ i, (fRh i).fv ⊆ range Rv) (hlam : lamh.fv ⊆ range Rv)
    (hdomR : domRh.fv ⊆ range Rv)
    (hω₀tg : ω₀ tg = 0) (A : State (Var 3) → Prop)
    (hR : ∃ ρ₁, Program.sem (Program.ode (jointSys (fun _ => Term.const 0) fRh lamh)
        (Formula.and domL' domRh)) ω₀ ρ₁ ∧ A ρ₁)
    (hQ : ∀ σ, A σ → σ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt σ) :
    faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq
        (Program.ode (jointSys (fun _ => Term.const 0) fRh lamh) (Formula.and domL' domRh))
        Q)
      φ tg dt ω₀ := by
  intro ν hplant
  obtain ⟨ρ₁, hhop, hρ₁A⟩ := hR
  have hrights : ∀ i : Fin 3, ν (Rv i) = ω₀ (Rv i) := by
    intro i
    refine sem_ode_mask hplant.1 ?_
    intro hb
    rcases clk_boundSet_sub _ _ (by simpa [ODESystem.boundSet] using hb) with hx | hx
    · obtain ⟨j, hj⟩ := leftBlock_boundSet_sub fL' hx
      exact absurd hj (by simp [Lv, Rv, Prod.ext_iff])
    · rw [Set.mem_singleton_iff] at hx
      exact absurd hx (by simp [Rv, Prod.ext_iff])
  have hνdomL : Formula.sat domL' ν := by
    obtain ⟨r, Φ, hr, hΦ0, hΦr, hder, hmask, hdom⟩ := hplant.1
    rw [← hΦr]
    exact hdom r (Set.right_mem_Icc.mpr hr)
  have hreplay := sem_frozen_replay hfR hlam hdomL hdomR hhop hrights hνdomL
  have hρ₁eq : rpatch ω₀ ρ₁ = ρ₁ := by
    funext v
    obtain ⟨s, i⟩ := v
    cases s with
    | R => rfl
    | L =>
        show ω₀ (Lv i) = ρ₁ (Lv i)
        exact (frozen_left_constant hhop i).symm
    | Aux =>
        show ω₀ ((Side.Aux, i) : Var 3) = ρ₁ ((Side.Aux, i) : Var 3)
        exact (sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ i)).symm
  have hplant' := plantT_rpatch hfL hdomL (ρ := ρ₁) hplant
  rw [hρ₁eq] at hplant'
  have hρ₁tg : ρ₁ tg = 0 := by
    rw [sem_ode_mask hhop (aux_not_jointSys_bound _ _ _ 1)]
    exact hω₀tg
  obtain ⟨μ, hQμSem, hQμφ⟩ := hQ ρ₁ hρ₁A hρ₁tg (rpatch ν ρ₁) hplant'
  refine ⟨μ, ?_, hQμφ⟩
  rw [Program.rename_refl] at hQμSem ⊢
  exact ⟨rpatch ν ρ₁, hreplay, hQμSem⟩

theorem hopA {fL' fRh : Fin 3 → Term (Var 3)} {lamh : Term (Var 3)}
    {domL' domRh : Formula (Var 3)} {φ : Formula (Var 3)} {Q : Program (Var 3)}
    {dt : ℝ} {ω₀ : State (Var 3)}
    (hfL : ∀ i, (fL' i).fv ⊆ range Lv) (hdomL : domL'.fv ⊆ range Lv)
    (hfR : ∀ i, (fRh i).fv ⊆ range Rv) (hlam : lamh.fv ⊆ range Rv)
    (hdomR : domRh.fv ⊆ range Rv)
    (hω₀tg : ω₀ tg = 0) (hdomLω : Formula.sat domL' ω₀) (A : State (Var 3) → Prop)
    (hR : ∃ ρ₁, Program.sem (Program.ode (rightBlock fRh lamh) domRh) ω₀ ρ₁ ∧ A ρ₁)
    (hQ : ∀ σ, A σ → σ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') Q φ tg dt σ) :
    faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL')
      (Program.seq (Program.ode (rightBlock fRh lamh) domRh) Q) φ tg dt ω₀ := by
  obtain ⟨ρ₁, hrun, hρ₁⟩ := hR
  have hj := repoPrefixA (φ := φ) (Q := Q) (dt := dt) hfL hdomL hfR hlam hdomR hω₀tg A
    ⟨ρ₁, hop_run_toJoint hfR hlam hdomL hdomLω hrun, hρ₁⟩ hQ
  refine faModalB_monoQ ?_ hj
  rintro ν μ ⟨κ, hhop, hQrun⟩
  exact ⟨κ, joint_run_toR hfR hlam hhop, hQrun⟩

theorem window1_of_B (fL' : Fin 3 → Term (Var 3)) (domL' : Formula (Var 3))
    (R R' : Program (Var 3)) (φ : Formula (Var 3)) (dt : ℝ) {σ : State (Var 3)}
    (heq : ∀ ν μ, Program.sem R ν μ ↔ Program.sem R' ν μ)
    (hb : faModalB (Equiv.refl (Var 3))
      (Program.ode (DLCalTiming.clk tg (leftBlock fL')) domL') R φ tg dt
      (Function.update σ tg 0)) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (windowSeg (leftBlock fL') domL' tg dt 1) R' φ) σ := by
  have hseg := (faModalB_clockedSeg_iff (leftBlock fL') domL' R φ tg dt σ).mpr hb
  exact sat_faModal_monoL
    (fun ν μ h => (sem_windowSeg_one (leftBlock fL') domL' tg dt).mp h)
    (sat_faModal_congrR heq hseg)

/-! ## The step provider -/

theorem gate (l : ℕ) (dt : ℝ) (R : Program (Var 3)) (ψ : Formula (Var 3))
    {σ : State (Var 3)}
    (hbody : Formula.sat (hostGuard vs 3 Side.L (mL l)) σ →
      Formula.sat (faModal (Equiv.refl (Var 3))
        (windowSeg (leftBlock (fL l)) domL tg dt 1) R ψ) σ) :
    Formula.sat (faModal (Equiv.refl (Var 3))
      (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1) R ψ) σ := by
  refine faModal_seqL _ _ _ _ _ _ ?_
  rw [sat_box]
  intro ν hν
  rw [sem_test] at hν
  obtain ⟨rfl, hg⟩ := hν
  exact hbody hg

theorem stayCase (l q : ℕ) (hl : l < 4) (hq : q < 4) (dt : ℝ) (hv : Verd l q)
    {σ : State (Var 3)} (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q)], ?_, by simp, by simp, ?_⟩
  · intro s hs
    rw [List.mem_singleton] at hs
    subst hs
    refine ⟨Gr_modeAt q (by omega), edge_mem q q ?_⟩
    interval_cases q <;> simp [edgeList]
  · refine gate l dt _ _ (fun hguard => ?_)
    have hanchor : Formula.sat (anchor l q) σ := by
      refine ⟨(sat_FM_append (g l) (gs l) _ σ).mpr ⟨hσ.1, ?_⟩, hσ.2⟩
      exact (atomTerms_iff (hiffL l hl) (hiffR q hq) σ).mpr
        ⟨hO1L l hl σ hguard, (sat_region_lt q hq σ).mp hreg⟩
    have := respond l q hl hq dt hv hanchor
    simpa [modeW, qfOf, edgeW] using this

/-! ## The dynamic right-only reposition to the deployed's zone -/

/-- The rows, evaluated. -/
theorem sat_FRow (l : ℕ) (hl : l < 4) (ω : State (Var 3)) :
    Formula.sat (FM (g l) (gs l)) ω ↔
      ω (Lv 0) - ω (Rv 0) ≤ 0 ∧ ω (Lv 1) - (ω (Rv 1) + mL' l) ≤ 0 := by
  rw [sat_FM_iff]
  rw [← eval_g l hl, ← eval_gs0 l hl]
  simp only [gs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.getD_cons_zero]

theorem upd_L (σ : State (Var 3)) (i : Fin 3) : Function.update σ tg 0 (Lv i) = σ (Lv i) :=
  Function.update_of_ne (by simp [Lv, Prod.ext_iff]) _ _
theorem upd_R (σ : State (Var 3)) (i : Fin 3) : Function.update σ tg 0 (Rv i) = σ (Rv i) :=
  Function.update_of_ne (by simp [Rv, Prod.ext_iff]) _ _

/-- **The landing.** A state whose lefts are the window start's, whose right speed and
odometer only grew, and which lies in the target zone `q'`'s atoms, satisfies the joint
anchor `(l, q')`: the row survives (`v_R`, `s_R` only increased), the left atoms are the
start's, the envelope holds. -/
theorem land (l q' : ℕ) (hl : l < 4) (hq' : q' < 4) {σ ρ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ) (hLat : CutSat (cL l) σ)
    (hρL : ∀ i, ρ (Lv i) = σ (Lv i)) (hv : σ (Rv 0) ≤ ρ (Rv 0))
    (hv2 : ρ (Rv 0) ≤ capL q') (hv3 : 3/10 ≤ ρ (Rv 0)) (hs : σ (Rv 1) ≤ ρ (Rv 1))
    (hs2 : loL q' ≤ ρ (Rv 1)) :
    Formula.sat (anchor l q') ρ := by
  have hrow := (sat_FRow l hl σ).mp hσ.1
  have hdL := (sat_domL σ).mp hσ.2.1
  have hLv := (cutSatL_val l hl σ).mp hLat
  have hc := cap_bounds q' hq'
  have hlo := lo_nonneg q' hq'
  refine ⟨(sat_FM_append (g l) (gs l) _ ρ).mpr ⟨(sat_FRow l hl ρ).mpr ?_,
    (atomTerms_iff (hiffL l hl) (hiffR q' hq') ρ).mpr ⟨?_, ?_⟩⟩,
    (sat_domL ρ).mpr ?_, (sat_domR ρ).mpr ?_⟩
  · rw [hρL 0, hρL 1]; constructor <;> linarith [hrow.1, hrow.2]
  · rw [cutSatL_val l hl ρ, hρL 0, hρL 1]; exact hLv
  · rw [cutSatR_val q' hq' ρ]; exact ⟨hs2, hv3, hv2⟩
  · rw [hρL 0, hρL 1]; exact hdL
  · exact ⟨by linarith, by linarith, by linarith⟩

/-- The joint piece `(l, q')`, anchored wherever its anchor holds with the clock at 0. -/
theorem piece (l q' : ℕ) (hl : l < 4) (hq' : q' < 4) (dt : ℝ) (hv : Verd l q') :
    ∀ τ, Formula.sat (anchor l q') τ → τ tg = 0 →
      faModalB (Equiv.refl (Var 3))
        (Program.ode (DLCalTiming.clk tg (leftBlock (fL l))) domL)
        (Program.ode (rightBlock (fR q') (Term.const 1)) domR) (anchor l q') tg dt τ := by
  intro τ hτ hτtg
  have hupd : Function.update τ tg 0 = τ := by
    funext x
    by_cases hx : x = tg
    · subst hx; rw [Function.update_self, hτtg]
    · rw [Function.update_of_ne hx]
  have := couple l q' hl hq' dt hv τ hτ
  rwa [hupd] at this

/-- **One-hop reposition**: from a right start in zone `q` (an earlier zone than the window's
certified target `q'`, edge `q → q'` declared, `c_q ≤ cap_{q'}`), run zone `q` alone until the
odometer reaches `q'`'s floor (`s_R = max(s₀, lo_{q'})`), take the edge, then the certified
joint piece `(l, q')`. -/
theorem hopCase (l q q' : ℕ) (hl : l < 4) (hq : q < 4) (hq' : q' < 4)
    (hedge : (q, q') ∈ edgeList) (hself : (q', q') ∈ edgeList) (hcap : capL q ≤ capL q')
    (dt : ℝ) (hv : Verd l q') {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g l) (gs l)) env) σ)
    (hreg : Formula.sat (region q) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = q) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  refine ⟨[(q, modeW q, edgeW q q'), (q', modeW q', edgeW q' q')], ?_, ?_, by simp, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨Gr_modeAt q (by omega), edge_mem q q' hedge⟩
    · exact ⟨Gr_modeAt q' (by omega), edge_mem q' q' hself⟩
  · exact (show List.IsChain (fun a b : ℕ × RMode (Var 3) × REdge (Var 3) => a.2.2.tgt = b.1)
        [(q', modeW q', edgeW q' q')] from by simp).cons (by
      intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      rfl)
  · refine gate l dt _ _ (fun hguard => ?_)
    have hLat := hO1L l hl σ hguard
    have hx0 := (cutSatR_val q hq σ).mp ((sat_region_lt q hq σ).mp hreg)
    have hdomL0 : Formula.sat domL (Function.update σ tg 0) := by
      rw [sat_domL, upd_L, upd_L]; exact (sat_domL σ).mp hσ.2.1
    have hdomR0 : Formula.sat domR (Function.update σ tg 0) := by
      rw [sat_domR, upd_R, upd_R]; exact (sat_domR σ).mp hσ.2.2
    have hb := hopA (fL' := fL l) (fRh := fR q) (lamh := Term.const 1) (domL' := domL)
      (domRh := domR) (φ := anchor l q')
      (Q := Program.ode (rightBlock (fR q') (Term.const 1)) domR) (dt := dt)
      (hfL l hl) hdomL (hfR q (by omega)) (by simp [Term.fv]) hdomR
      (Function.update_self _ _ _) hdomL0 (fun ρ => Formula.sat (anchor l q') ρ)
      (by
        obtain ⟨ρ, hrun, hρs, hρv1, hρv2, hρo⟩ := mode_reach q hq (loL q') _ hdomR0
          (by rw [upd_R]; exact hx0.2.1) (by rw [upd_R]; exact hx0.2.2)
        rw [upd_R] at hρs hρv1
        refine ⟨ρ, hrun, land l q' hl hq' hσ hLat ?_ hρv1 (le_trans hρv2 hcap)
          (le_trans hx0.2.1 hρv1) ?_ ?_⟩
        · intro i
          rw [hρo (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            upd_L]
        · rw [hρs]; exact le_max_left _ _
        · rw [hρs]; exact le_max_right _ _)
      (piece l q' hl hq' dt hv)
    have hw := window1_of_B (fL l) domL _
      (bigSeq [Program.ode (rightBlock (fR q) (Term.const 1)) domR,
        Program.ode (rightBlock (fR q') (Term.const 1)) domR]) (anchor l q') dt
      (fun ν μ => sem_foldr_seq_bigSeq [Program.ode (rightBlock (fR q) (Term.const 1)) domR]
        (Program.ode (rightBlock (fR q') (Term.const 1)) domR) ν μ) hb
    have := sat_faModal_monoPost (anchor_post l q' hl hq') hw
    simpa [modeW, qfOf, edgeW] using this

/-- **Two-hop reposition** (a `SLOW` right start of the `FAST` window; `SLOW` has no edge to
`FAST`): run `SLOW` alone up to `s_R = max(s₀, 50)`, the edge `SLOW → MEDIUM_ECO`, run
`MEDIUM_ECO` (zero duration: the odometer is already past 50), the edge
`MEDIUM_ECO → FAST`, the certified joint piece `(FAST, FAST)`. -/
theorem twoHopCase (dt : ℝ) (hv : Verd 3 3) {σ : State (Var 3)}
    (hσ : Formula.sat (Formula.and (FM (g 3) (gs 3)) env) σ)
    (hreg : Formula.sat (region 0) σ) :
    ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
      (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
      List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
      (∀ s, segs.head? = some s → s.1 = 0) ∧
      Formula.sat (faModal (Equiv.refl (Var 3))
        (gwindowSeg (hostGuard vs 3 Side.L (mL 3)) (leftBlock (fL 3)) domL tg dt 1)
        (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
        (Formula.and (Formula.and (FM (g 3) (gs 3)) env) (region (qfOf segs 0)))) σ := by
  refine ⟨[(0, modeW 0, edgeW 0 1), (1, modeW 1, edgeW 1 3), (3, modeW 3, edgeW 3 3)],
    ?_, ?_, by simp, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨Gr_modeAt 0 (by norm_num), edge_mem 0 1 (by simp [edgeList])⟩
    · exact ⟨Gr_modeAt 1 (by norm_num), edge_mem 1 3 (by simp [edgeList])⟩
    · exact ⟨Gr_modeAt 3 (by norm_num), edge_mem 3 3 (by simp [edgeList])⟩
  · refine List.IsChain.cons (List.IsChain.cons (by simp) ?_) ?_ <;>
    · intro y hy
      rw [List.head?_cons, Option.mem_some_iff] at hy
      subst hy
      rfl
  · refine gate 3 dt _ _ (fun hguard => ?_)
    have hLat := hO1L 3 (by norm_num) σ hguard
    have hx0 := (cutSatR_val 0 (by norm_num) σ).mp ((sat_region_lt 0 (by norm_num) σ).mp hreg)
    have hdomL0 : Formula.sat domL (Function.update σ tg 0) := by
      rw [sat_domL, upd_L, upd_L]; exact (sat_domL σ).mp hσ.2.1
    have hdomR0 : Formula.sat domR (Function.update σ tg 0) := by
      rw [sat_domR, upd_R, upd_R]; exact (sat_domR σ).mp hσ.2.2
    have hc0 : capL 0 = 3/5 := by norm_num [capL, capQ]
    have hc1 : capL 1 = 9/10 := by norm_num [capL, capQ]
    have hc3 : capL 3 = 3/2 := by norm_num [capL, capQ]
    have hlo3 : loL 3 = 50 := by norm_num [loL, loQ]
    let EC := Program.ode (rightBlock (fR 1) (Term.const 1)) domR
    let FA := Program.ode (rightBlock (fR 3) (Term.const 1)) domR
    have hb := hopA (fL' := fL 3) (fRh := fR 0) (lamh := Term.const 1) (domL' := domL)
      (domRh := domR) (φ := anchor 3 3) (Q := Program.seq EC FA) (dt := dt)
      (hfL 3 (by norm_num)) hdomL (hfR 0 (by norm_num)) (by simp [Term.fv]) hdomR
      (Function.update_self _ _ _) hdomL0
      (fun ρ => Formula.sat domL ρ ∧ ∃ ρ₂, Program.sem EC ρ ρ₂ ∧ Formula.sat (anchor 3 3) ρ₂)
      (by
        obtain ⟨ρ₁, hrun₁, hρ₁s, hρ₁v1, hρ₁v2, hρ₁o⟩ := mode_reach 0 (by norm_num) 50 _ hdomR0
          (by rw [upd_R]; exact hx0.2.1) (by rw [upd_R]; exact hx0.2.2)
        rw [upd_R] at hρ₁s hρ₁v1
        have hρ₁L : ∀ i, ρ₁ (Lv i) = σ (Lv i) := by
          intro i
          rw [hρ₁o (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            upd_L]
        have hv1 : 3/10 ≤ ρ₁ (Rv 0) := le_trans hx0.2.1 hρ₁v1
        have hs1 : 50 ≤ ρ₁ (Rv 1) := by rw [hρ₁s]; exact le_max_right _ _
        have hρ₁dom : Formula.sat domR ρ₁ := by
          rw [sat_domR]
          refine ⟨by linarith, by rw [hc0] at hρ₁v2; linarith, by linarith⟩
        obtain ⟨ρ₂, hrun₂, hρ₂s, hρ₂v1, hρ₂v2, hρ₂o⟩ := mode_reach 1 (by norm_num) 50 _ hρ₁dom
          hv1 (by rw [hc1]; rw [hc0] at hρ₁v2; linarith)
        refine ⟨ρ₁, hrun₁, ?_, ρ₂, hrun₂, land 3 3 (by norm_num) (by norm_num) hσ hLat ?_ ?_ ?_
          ?_ ?_ ?_⟩
        · rw [sat_domL, hρ₁L 0, hρ₁L 1]; exact (sat_domL σ).mp hσ.2.1
        · intro i
          rw [hρ₂o (Lv i) ⟨by simp [Lv, Rv, Prod.ext_iff], by simp [Lv, Rv, Prod.ext_iff]⟩,
            hρ₁L i]
        · exact le_trans hρ₁v1 hρ₂v1
        · rw [hc3]; rw [hc1] at hρ₂v2; linarith
        · exact le_trans hv1 hρ₂v1
        · rw [hρ₂s, hρ₁s]; exact le_trans (le_max_left _ _) (le_max_left _ _)
        · rw [hρ₂s, hlo3]; exact le_trans hs1 (le_max_left _ _))
      (by
        rintro τ ⟨hτL, hτex⟩ hτtg
        exact hopA (hfL 3 (by norm_num)) hdomL (hfR 1 (by norm_num)) (by simp [Term.fv])
          hdomR hτtg hτL (fun ρ => Formula.sat (anchor 3 3) ρ) hτex
          (piece 3 3 (by norm_num) (by norm_num) dt hv))
    have hw := window1_of_B (fL 3) domL _
      (bigSeq [Program.ode (rightBlock (fR 0) (Term.const 1)) domR, EC, FA]) (anchor 3 3) dt
      (fun ν μ => sem_foldr_seq_bigSeq
        [Program.ode (rightBlock (fR 0) (Term.const 1)) domR, EC] FA ν μ) hb
    have := sat_faModal_monoPost (anchor_post 3 3 (by norm_num) (by norm_num)) hw
    simpa [modeW, qfOf, edgeW, EC, FA] using this

/-- Left zone `l`'s window, every right start (the emitted cover): stay in a jointOK start;
reposition from an earlier zone; `STALL` excluded by its (false) region. -/
theorem HmultiL (l : ℕ) (hl : l < 4) (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
    ∀ (q : ℕ), q < Gr.modes.length → ∀ σ, σ mv = (q : ℝ) →
      Formula.sat (Formula.and (Formula.and (FM (g l) (gs l)) env) (region q)) σ →
      ∃ segs : List (ℕ × RMode (Var 3) × REdge (Var 3)),
        (∀ s ∈ segs, Gr.modeAt s.1 = some s.2.1 ∧ s.2.2 ∈ Gr.edgesFrom s.1) ∧
        List.IsChain (fun a b => a.2.2.tgt = b.1) segs ∧
        (∀ s, segs.head? = some s → s.1 = q) ∧
        Formula.sat (faModal (Equiv.refl (Var 3))
          (gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1)
          (bigSeq (segs.map (fun s => Program.ode s.2.1.sys s.2.1.dom)))
          (Formula.and (Formula.and (FM (g l) (gs l)) env) (region (qfOf segs q)))) σ := by
  intro q hq σ _ hσ
  rw [Gr_len] at hq
  have hc : ∀ a b : ℕ, a < 4 → b < 4 → capQ a ≤ capQ b → capL a ≤ capL b := by
    intro a b _ _ h; unfold capL; exact_mod_cast h
  interval_cases l
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact stayCase 0 0 (by norm_num) (by norm_num) dt h00 hσ.1 hσ.2
    | 1, _, hσ =>
      exact stayCase 0 1 (by norm_num) (by norm_num) dt h01 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 0 2 (by norm_num) (by norm_num) dt h02 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 0 3 (by norm_num) (by norm_num) dt h03 hσ.1 hσ.2
    | 4, _, hσ =>
      exact absurd hσ.2 (not_sat_region_sink 4 (by norm_num) σ)
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact hopCase 1 0 1 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 0 1 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h11 hσ.1 hσ.2
    | 1, _, hσ =>
      exact stayCase 1 1 (by norm_num) (by norm_num) dt h11 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 1 2 (by norm_num) (by norm_num) dt h12 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 1 3 (by norm_num) (by norm_num) dt h13 hσ.1 hσ.2
    | 4, _, hσ =>
      exact absurd hσ.2 (not_sat_region_sink 4 (by norm_num) σ)
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact hopCase 2 0 2 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 0 2 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h22 hσ.1 hσ.2
    | 1, _, hσ =>
      exact hopCase 2 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 1 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h23 hσ.1 hσ.2
    | 2, _, hσ =>
      exact stayCase 2 2 (by norm_num) (by norm_num) dt h22 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 2 3 (by norm_num) (by norm_num) dt h23 hσ.1 hσ.2
    | 4, _, hσ =>
      exact absurd hσ.2 (not_sat_region_sink 4 (by norm_num) σ)
  · match q, hq, hσ with
    | 0, _, hσ =>
      exact twoHopCase dt h33 hσ.1 hσ.2
    | 1, _, hσ =>
      exact hopCase 3 1 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 1 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h33 hσ.1 hσ.2
    | 2, _, hσ =>
      exact hopCase 3 2 3 (by norm_num) (by norm_num) (by norm_num)
        (by simp [edgeList]) (by simp [edgeList]) (hc 2 3 (by norm_num) (by norm_num)
          (by norm_num [capQ])) dt h33 hσ.1 hσ.2
    | 3, _, hσ =>
      exact stayCase 3 3 (by norm_num) (by norm_num) dt h33 hσ.1 hσ.2
    | 4, _, hσ =>
      exact absurd hσ.2 (not_sat_region_sink 4 (by norm_num) σ)

/-! ## The declared rows, per left mode -/

noncomputable def FRow (l : ℕ) : Formula (Var 3) := FM (g l) (gs l)
noncomputable def ϕRow (l : ℕ) : RFormula (Var 3) := canonInvM (g l) (gs l)

theorem encode_ϕRow (l : ℕ) : encode (Equiv.refl (Var 3)) (ϕRow l) = FRow l :=
  encode_canonInvM _ _

theorem aux_notin_FRow (a : Fin 3) (l : ℕ) : ((Side.Aux, a) : Var 3) ∉ (FRow l).fv :=
  notMem_FM_fv (fun g' hg' hx => by
    rcases comps_fv_all l g' hg' hx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact absurd hi (by simp [Lv, Prod.ext_iff])
    · exact absurd hi (by simp [Rv, Prod.ext_iff]))

/-! ## The left automaton, from the file -/

def nextL : List (List ℕ) :=
  (List.range 4).map (fun l =>
    (mL l).next.filterMap (Handoff.leftModeIndex rover_patrol_zones_IRv2))

/-- `SLOW → [MEDIUM_ECO, MEDIUM_BRISK, SLOW]`, `MEDIUM_ECO → [FAST, MEDIUM_BRISK, MEDIUM_ECO]`,
`MEDIUM_BRISK → [FAST, MEDIUM_ECO, MEDIUM_BRISK]`, `FAST → [FAST]`. -/
theorem nextL_eq : nextL = [[1, 2, 0], [3, 2, 1], [3, 1, 2], [3]] := by decide

theorem nextL_transitions :
    ((List.range 4).flatMap (fun m' => (nextL.getD m' []).map (fun t => (m', t))))
      = Handoff.transitions rover_patrol_zones_IRv2 := by decide

noncomputable def guardsL : List (Formula (Var 3)) :=
  (List.range 4).map (fun l => hostGuard vs 3 Side.L (mL l))

noncomputable def A (dt : ℝ) : LeftAut 3 :=
  { windows := (List.range 4).map (fun l =>
      gwindowSeg (hostGuard vs 3 Side.L (mL l)) (leftBlock (fL l)) domL tg dt 1),
    guards := guardsL,
    next := nextL }

theorem A_numModes (dt : ℝ) : (A dt).numModes = 4 := rfl

theorem A_window (dt : ℝ) (t : ℕ) (ht : t < 4) :
    (A dt).window t = gwindowSeg (hostGuard vs 3 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1 := by
  interval_cases t <;> rfl

theorem A_guard (dt : ℝ) (t : ℕ) (ht : t < 4) :
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

/-! ## Freshness of `u_L` and `mv` -/

theorem hulenv : uL ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 2 (hdomL h)
  · exact aux_notin_range_Rv 2 (hdomR h)

theorem hmvenv : mv ∉ env.fv := fun h => by
  rcases h with h | h
  · exact aux_notin_range_Lv 0 (hdomL h)
  · exact aux_notin_range_Rv 0 (hdomR h)

theorem hmvreg : ∀ q, mv ∉ (region q).fv := by
  intro q h
  by_cases hq : q < 5
  · exact aux_notin_range_Rv 0 (region_fv q hq h)
  · simp only [region, show ¬ q < 4 from by omega, if_false] at h
    simp [Formula.fv, Term.fv] at h

theorem hulBk : uL ∉ (mvRegion mv region Gr.modes.length).fv := fun h => by
  rcases mvRegion_fv_sub mv region Gr.modes.length (fun q hq => region_fv q hq) h with h | h
  · exact absurd (Set.mem_singleton_iff.mp h) (by decide)
  · exact aux_notin_range_Rv 2 h

theorem hulG (dt : ℝ) : ∀ t, uL ∉ ((A dt).guard t).fv := by
  intro t h
  by_cases ht : t < 4
  · exact aux_notin_range_Lv 2 (hgrd dt t ht h)
  · have : (A dt).guard t = Formula.tt := by
      unfold LeftAut.guard A guardsL
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this] at h
    exact absurd h (by simp [Formula.fv])

theorem framesGw (t : ℕ) (dt : ℝ) (a : Fin 3) (ha : a ≠ 1) :
    FramesMv (gwindowSeg (hostGuard vs 3 Side.L (mL t)) (leftBlock (fL t)) domL tg dt 1)
      ((Side.Aux, a) : Var 3) := by
  refine framesMv_gwindow _ (fL t) domL tg dt 1 _ (by simpa [Prod.ext_iff] using ha) ?_
  intro h
  obtain ⟨i, hi⟩ := leftBlock_bound_sub (fL t) _ h
  exact aux_ne_Lv a i hi

theorem hframesUl (dt : ℝ) : ∀ t, FramesMv ((A dt).window t) uL := by
  intro t
  by_cases ht : t < 4
  · rw [A_window dt t ht]
    exact framesGw t dt 2 (by decide)
  · have : (A dt).window t = Program.test (Formula.neg Formula.tt) := by
      unfold LeftAut.window A
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]
    exact framesMv_test _ _

theorem hulR : uL ∉ (rightAutomatonBody Gr mv).bv :=
  notMem_bv_rightAutomatonBody Gr mv uL (by decide) (aux_notin_range_Rv 2) htt hRv

/-! ## The handoffs, in-kernel: the odometer margin only loosens along the route -/

theorem handoff (dt : ℝ) : ∀ m' < (A dt).numModes, ∀ t ∈ (A dt).succ m', ∀ ω,
    Formula.sat (FRow m') ω → Formula.sat env ω → Formula.sat ((A dt).guard t) ω →
      Formula.sat (FRow t) ω := by
  intro m' hm' t ht ω hF _ _
  rw [A_numModes] at hm'
  rw [A_succ, nextL_eq] at ht
  have ht4 : t < 4 := by interval_cases m' <;> simp at ht <;> omega
  have hm : mL' m' ≤ mL' t := by
    interval_cases m' <;> simp at ht <;> rcases ht with rfl | rfl | rfl <;>
      norm_num [mL', mQ]
  rw [FRow, sat_FRow m' hm'] at hF
  rw [FRow, sat_FRow t ht4]
  exact ⟨hF.1, by linarith [hF.2]⟩

/-! ## The per-mode steps -/

theorem hstepM (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
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
  exact hstepMode_multiR Gr mv (FRow t) env region _ (aux_notin_FRow 0 t) hmvenv hmvreg
    hfresh htt hlt (framesGw t dt 0 (by decide))
    (HmultiL t ht dt h00 h01 h02 h03 h11 h12 h13 h22 h23 h33)

/-! ## Theorem 3, mode-keyed -/

/-- **`rover_patrol_zones` (suite_v2), Theorem 3 at the DECLARED mode-dependent invariant.**
Left: the automaton of the file (`SLOW → [MEDIUM_ECO, MEDIUM_BRISK, SLOW]`,
`MEDIUM_ECO → [FAST, MEDIUM_BRISK, MEDIUM_ECO]`, `MEDIUM_BRISK → [FAST, MEDIUM_ECO,
MEDIUM_BRISK]`, `FAST → [FAST]`; the worn deployed rover `v' = 1.25 (0.8 c − v)`, `s' = v`),
each step `?guard_t ; u_L := t ; ?guard_t ; window_t` with `u_L = (Aux, 2)`; right: the
five-mode reference automaton of the file (the zones `v' = c − v`, `c = 0.6/0.9/1.1/1.5`,
and the `STALL` fallback; declared edges, the four pruned zone `→ STALL` edges included). The
loop invariant keys the declared rows by `u_L` (`v_L ≤ v_R ∧ s_L ≤ s_R + m`, `m = 0.5, 1, 1,
2`), plus the evolve envelope (`v ∈ [0, 1.6]`, `s ≥ 0`; no odometer wall, §19 of
`docs/SUITE-REDESIGN.md`) on both sides and the right mode's region — the zone's kept cut
atoms (`s ≥ floor`, `0.3 ≤ v ≤ cap`), `STALL` excluded (the pruned sink: the right is never
in it). Response (the emitted cover): in every left window, STAY in a jointOK start zone on
the certified joint segment at λ = 1; from an earlier zone, reposition right-only (the
explicit zone run, until the odometer reaches the target zone's floor; from `SLOW` in the
`FAST` window via `MEDIUM_ECO`) and then the certified joint piece in the target zone.
Handoffs in-kernel (the margin only grows along the route). Staying of every kept atom is
rational (the own field's sign); existence is the explicit zone solution. Residuals: ten
stratified verdict packs `Verd l q` (left window `l` at its own row, `modalVerdX`, the tool's
own narrowed queries). -/
theorem rover_patrol_zones_modeKeyed (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (h33 : Verd 3 3) :
    RFormula.rvalid (theorem3Form
      (leftAutomatonBody (A dt) uL)
      (rightAutomatonBody Gr mv)
      (psiK uL ϕRow (A dt).numModes domL domR
        (mvRegionR mv region Gr.modes.length))) := by
  refine theorem3_modeKeyed (A dt) uL Gr mv FRow ϕRow domL domR
    (mvRegion mv region Gr.modes.length) (mvRegionR mv region Gr.modes.length)
    encode_ϕRow (encode_mvRegionR _ _ _) ?_ ?_ ?_
  · exact hd_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) (hwin dt) (hgrd dt)
      (hnext dt) htt hRv
  · exact hstep_modeKeyed (A dt) uL (rightAutomatonBody Gr mv) FRow env
      (mvRegion mv region Gr.modes.length) (aux_notin_FRow 2) hulenv hulBk (hulG dt)
      (hframesUl dt) hulR (hnext dt)
      (hstepM dt h00 h01 h02 h03 h11 h12 h13 h22 h23 h33) (handoff dt)
  · exact hddF_modeKeyed (A dt) Gr 0 1 2 (by decide) (by decide) ϕRow domL domR
      (mvRegionR mv region Gr.modes.length) (hwin dt) (hgrd dt) (hnext dt) htt hRv
      (fun m _ => canonInvM_varsL (g m) (gs m) (comps_fv_all m))
      (fun m _ => canonInvM_varsR (g m) (gs m)) hdomL hdomR rfl
      (fun v hv => mvRegion_fv_sub mv region Gr.modes.length (fun q hq => region_fv q hq) hv)

end V2RoverPatrolZones
end RelCertifier

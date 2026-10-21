/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_linkloss`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`platoon_delay_linkloss_wellFormedR`, Z3-free):

* `FOLLOW` (`20 ≤ g < 40`, `g' = −0.5 (g − 30)`) and `CATCH` (`g ≥ 30`, `g' = −0.6 (g − 30)`):
  contractions toward 30 whose guard sets are forward invariant (style (a));
* `BRAKE` (`g < 20`, `g' = 1.5`, declared successors `[BRAKE, FOLLOW]`; the brake
  re-engages `FOLLOW` once the gap is back at 20 m, the 2026-10-10 repair,
  `docs/SUITE-REDESIGN.md` §21): style (b). A run of duration `t ≤ 1` from `g < 20` ends at
  `g₀ ≤ g(t) ≤ g₀ + 1.5 t < 21.5`: in `BRAKE`'s guard if below 20, else in `FOLLOW`'s
  (`20 ≤ g < 40`). Existence: the linear motion `g₀ + 1.5 t` stays in `0 ≤ g ≤ 60`.

(Until 2026-10-10 `BRAKE`'s only successor was itself and the model was refuted here, from
`g = 19`: the run of duration 1 ends at `g = 20.5`.)
-/
import RelCertifier.Proofs.Encoding.CutRespond
import RelCertifier.Proofs.Encoding.GuardedSwitch
import RelCertifier.Proofs.Encoding.ModeHandoff
import RelCertifier.Proofs.Flow.FaceBridge
import RelCertifier.InstancesV2.BenchIR.platoon_delay_linkloss
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2PlatoonDelayLinkloss

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["g"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := platoon_delay_linkloss_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
noncomputable def comps (l : ℕ) : List (Term (Var 3)) :=
  hostComps vs 3 (platoon_delay_linkloss_IRv2.invariants.getD l ("", PForm.tt)).2
noncomputable def g (l : ℕ) : Term (Var 3) := (comps l).getD 0 (Term.const 0)
theorem hp05m : Run.parseRat "-0.5" = some (-(1:ℚ)/2) := by
  have h : parseQ "-0.5" = some (⟨-5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp06m : Run.parseRat "-0.6" = some (-(3:ℚ)/5) := by
  have h : parseQ "-0.6" = some (⟨-6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp15 : Run.parseRat "1.5" = some ((3:ℚ)/2) := by
  have h : parseQ "1.5" = some (⟨15, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
/-- Right fields (FOLLOW, CATCH): `g' = k_q (30 − g)`. -/
noncomputable def kR (q : ℕ) : ℝ := if q = 1 then 3/5 else 1/2

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (30 - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp300, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR] <;> ring

theorem fR_pad (q : ℕ) (hq : q < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  fin_cases i
  · exact absurd rfl hi
  all_goals interval_cases q <;>
    simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp05m,
      hp06m, hp300, hp15, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 60) := by
  simp only [domR, hostEvolve, mR, platoon_delay_linkloss_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp600, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (FOLLOW 0, CATCH 1, BRAKE 2). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 1), (0, 0), (0, 2), (1, 0), (1, 1), (2, 2), (2, 0)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_len : Gr.modes.length = 3 := rfl

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The non-sink right guards, evaluated (`FOLLOW`: `20 ≤ g < 40`; `CATCH`: `g ≥ 30`). -/
theorem sat_guardR (q : ℕ) (hq : q < 2) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔
      (if q = 0 then 20 ≤ ν (Rv 0) ∧ ν (Rv 0) < 40 else 30 ≤ ν (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mR, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp200, hp400,
      hp300, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]


theorem epsR_eq : epsR platoon_delay_linkloss_IRv2 = 1 := by
  simp [epsR, platoon_delay_linkloss_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem fR0_brake (x : State (Var 3)) : Term.eval (fR 2 0) x = 3/2 := by
  simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp15,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_guardR2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ ν (Rv 0) < 20 := by
  simp [hostGuard, mR, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp200, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 3)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `FOLLOW` and `CATCH`** (style (a), Z3-free). -/
theorem platoon_delay_linkloss_wellFormedR_modes (q : ℕ) (hq : q < 2) :
    WellFormedRMode Gr guardR (epsR platoon_delay_linkloss_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hgx := (sat_guardR q hq x).mp hg
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) 30 hk (fR0_eval q hq)
      (fun i hi s => fR_pad q (by omega) i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 (by norm_num)) h1, le_trans h2 (max_le hdx.2 (by norm_num))⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (30 - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq]
    have hb := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- FOLLOW: [20, 40) invariant
      simp only [if_true] at hgx
      exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
        (by simp only [if_true]; exact ⟨le_trans (le_min hgx.1 (by norm_num)) hb.1,
          lt_of_le_of_lt hb.2 (max_lt hgx.2 (by norm_num))⟩)⟩
    · -- CATCH: g ≥ 30 invariant
      norm_num at hgx
      exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
        (by norm_num; exact le_trans (le_min hgx le_rfl) hb.1)⟩

/-- **Assumption 1 at `BRAKE`** (style (b)): the gap reopens at `1.5 m/s`; every run of at
most one interval ends below `21.5`, in `BRAKE`'s guard or in `FOLLOW`'s. -/
theorem platoon_delay_linkloss_wellFormedR_brake :
    WellFormedRMode Gr guardR (epsR platoon_delay_linkloss_IRv2) 2 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hgx := (sat_guardR2 x).mp hg
  refine ⟨⟨_, exists_rate_run (fR := fR 2) (domR := domR) x 0 (3/2) fR0_brake
    (fun i hi s => fR_pad 2 (by norm_num) i hi s) 1 (by norm_num) (fun t ht ht1 => ?_)⟩, ?_⟩
  · show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    constructor <;> nlinarith [hdx.1, hdx.2]
  · intro t Φ ht H
    have hup := H.rate_le (memR 2) (3/2) (fun s _ => by rw [eval_unit_mul, fR0_brake])
    have hlo := H.mono (memR 2) (fun s _ => by rw [eval_unit_mul, fR0_brake]; norm_num)
    have ht0 := H.hr
    by_cases h20 : Φ t (Rv 0) < 20
    · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR2 _).mpr h20⟩
    · push_neg at h20
      refine ⟨edgeW 2 0, edge_mem 2 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr ?_⟩
      rw [if_pos rfl]
      exact ⟨h20, by nlinarith⟩

/-- **`platoon_delay_linkloss` satisfies Assumption 1** (every mode, Z3-free). -/
theorem platoon_delay_linkloss_wellFormedR :
    WellFormedR Gr guardR (epsR platoon_delay_linkloss_IRv2) := by
  intro q hq
  rw [Gr_len] at hq
  rcases (by omega : q < 2 ∨ q = 2) with h | rfl
  · exact platoon_delay_linkloss_wellFormedR_modes q h
  · exact platoon_delay_linkloss_wellFormedR_brake

end V2PlatoonDelayLinkloss
end RelCertifier

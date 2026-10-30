/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two breath phases and their declared `next` lists), the lowered right guards, and
`ε_r = 0.01` read from the file.

The right model is the breath with a sealed cuff: the inspiratory countdown timer `s`
(coordinate 0; `s' = −1` in `INSP`, `s' = 0` in `EXP`) and the lung volume `V` (coordinate 1);
coordinate 2 is the padding of the bridge's keyed records (field 0, frozen). Evolve domain:
`s ≥ 0`, `V ≥ −0.4`.
`INSP` (`s ≥ 0.01`): `V' = 0.4`; `EXP` (`s < 0.01`): `V' = −1.923077 V`.
* Existence (i), `INSP`: the linear run `(s₀ − u, V₀ + 0.4 u)`. The timer stays `≥ 0` for one
  period `u ≤ ε_r = 0.01` since it starts at `s₀ ≥ 0.01` (exactly one period of headroom), and
  `V` only rises. `EXP`: the frozen timer and the exponential decay of `V` toward 0; `V` stays
  between `V₀` and 0, so above `min V₀ 0 ≥ −0.4`.
* (ii): `INSP` ends in the domain, where `s ≥ 0.01` is `INSP`'s guard and `s < 0.01` is `EXP`'s
  (style (b), exit); `EXP`: the timer is constant (`s' = 0`), so `s < 0.01` is kept (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.ventilator_vc_cuffleak

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2VentilatorVcCuffleak

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["s", "V"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := ventilator_vc_cuffleak_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_m0_4 : Run.parseRat "-0.4" = some ((-2:ℚ)/5) := by
  have h : parseQ "-0.4" = some (⟨-4, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_4 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m1_0 : Run.parseRat "-1.0" = some (-1 : ℚ) := by
  have h : parseQ "-1.0" = some (⟨-10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_923077 : Run.parseRat "1.923077" = some ((1923077:ℚ)/1000000) := by
  have h : parseQ "1.923077" = some (⟨1923077, 1000000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_01 : Run.parseRat "0.01" = some ((1:ℚ)/100) := by
  have h : parseQ "0.01" = some (⟨1, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- The expiratory rate `1.923077` (`1 / ((R_aw + R_tube) C)` as written). -/
noncomputable def kE : ℝ := 1923077 / 1000000

/-- The timer's field: `−1` in `INSP` (counting down), `0` in `EXP` (held). -/
theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) :
    Term.eval (fR q 0) x = if q = 0 then -1 else 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fI0_eval (x : State (Var 3)) : Term.eval (fR 0 0) x = -1 := by
  simpa using fR0_eval 0 (by norm_num) x

theorem fE0_eval (x : State (Var 3)) : Term.eval (fR 1 0) x = 0 := by
  simpa using fR0_eval 1 (by norm_num) x

theorem fI1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 2/5 := by
  simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fE1_eval (x : State (Var 3)) : Term.eval (fR 1 1) x = kE * (0 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv, kE] <;> ring

/-- The padding coordinate 2 (not in `vs`): its right field lowers to 0. -/
theorem fR2_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ -2/5 ≤ x (Rv 1)) := by
  simp only [domR, hostEvolve, mR, ventilator_vc_cuffleak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, AOp.interp, Rv,
    and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (INSP 0, EXP 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  have hlen : q < 2 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 2 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (1/100 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 0) ∧ -2/5 ≤ ν (Rv 1)) := by
  simp [hostGuard, mR, ventilator_vc_cuffleak_IRv2, Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (ν (Rv 0) < 1/100 ∧ 0 ≤ ν (Rv 0) ∧ -2/5 ≤ ν (Rv 1)) := by
  simp [hostGuard, mR, ventilator_vc_cuffleak_IRv2, Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_m1_0, hp_1_923077, hp_0_01, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR ventilator_vc_cuffleak_IRv2 = 1/100 := by
  simp [epsR, ventilator_vc_cuffleak_IRv2, hp_0_01]

/-! ## Existence: the explicit runs -/

theorem lin_der (a b t : ℝ) : HasDerivAt (fun u => a + b * u) b t := by
  simpa using ((hasDerivAt_id t).const_mul b).const_add a

/-- The run of `INSP` from `x`: the timer counting down and the delivered volume at 0.4 L/s. -/
noncomputable def phiI (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + -1 * t
  else if i.val = 1 then x (Rv 1) + 2/5 * t
  else x (Rv 2)

/-- The run of `EXP` from `x`: the held timer and the passive emptying. -/
noncomputable def phiE (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0)
  else if i.val = 1 then 0 + (x (Rv 1) - 0) * Real.exp (-(kE * t))
  else x (Rv 2)

theorem phiI_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiI x i) (Term.eval (fR 0 i) (trajRs x (phiI x) t)) t := by
  match i with
  | 0 =>
      rw [fI0_eval]
      have hf : phiI x 0 = fun u => x (Rv 0) + -1 * u := by funext u; simp [phiI]
      rw [hf]; exact lin_der _ _ t
  | 1 =>
      rw [fI1_eval]
      have hf : phiI x 1 = fun u => x (Rv 1) + 2/5 * u := by funext u; simp [phiI]
      rw [hf]; exact lin_der _ _ t
  | 2 =>
      rw [fR2_eval 0 (by norm_num)]
      have hf : phiI x 2 = fun _ => x (Rv 2) := by funext u; simp [phiI]
      rw [hf]; exact hasDerivAt_const _ _

theorem phiE_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiE x i) (Term.eval (fR 1 i) (trajRs x (phiE x) t)) t := by
  match i with
  | 0 =>
      rw [fE0_eval]
      have hf : phiE x 0 = fun _ => x (Rv 0) := by funext u; simp [phiE]
      rw [hf]; exact hasDerivAt_const _ _
  | 1 =>
      rw [fE1_eval, trajRs_R]
      have hf : phiE x 1 = fun u => 0 + (x (Rv 1) - 0) * Real.exp (-(kE * u)) := by
        funext u; simp [phiE]
      rw [hf]
      exact hasDerivAt_expApproach kE 0 (x (Rv 1)) t
  | 2 =>
      rw [fR2_eval 1 (by norm_num)]
      have hf : phiE x 2 = fun _ => x (Rv 2) := by funext u; simp [phiE]
      rw [hf]; exact hasDerivAt_const _ _

/-- **`INSP`'s run** from a guard state: the timer starts at `s₀ ≥ 0.01`, so it stays `≥ 0`
for one period `ε_r = 0.01`; `V` rises. -/
theorem exists_runI (x : State (Var 3)) (hd : Formula.sat domR x) (hs : 1/100 ≤ x (Rv 0)) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x (1/100) Φ := by
  obtain ⟨a0, a1⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiI x) (1/100) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiI_der x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiI]
    | 1 => simp [phiI]
    | 2 => simp [phiI]
  · rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiI, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    refine ⟨by linarith, by linarith⟩

theorem exists_runE (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x ε Φ := by
  obtain ⟨a0, a1⟩ := (sat_domR x).mp hd
  have hk : 0 ≤ kE := by unfold kE; norm_num
  refine ⟨_, trajRs_sol x (phiE x) ε hε (fun i => ?_) (fun i t _ _ => phiE_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiE]
    | 1 => simp [phiE]
    | 2 => simp [phiE]
  · obtain ⟨l, _⟩ := exp_approach_between kE 0 (x (Rv 1)) t hk ht
    rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiE, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    exact ⟨a0, le_trans (le_min a1 (by norm_num)) l⟩

/-- **Assumption 1 for `ventilator_vc_cuffleak`**, every mode, Z3-free. -/
theorem ventilator_vc_cuffleak_wellFormedR :
    WellFormedR Gr guardR (epsR ventilator_vc_cuffleak_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- INSP: the run ends in the domain; `s ≥ 0.01` is INSP, `s < 0.01` is EXP
    have hg0 := (sat_guard0 x).mp hg
    refine ⟨exists_runI x hd hg0.1, ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : 1/100 ≤ Φ t (Rv 0)
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h1, e0, e1⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, e0, e1⟩⟩
  · -- EXP: the timer is held (`s' = 0`), so `s < 0.01` is kept
    refine ⟨exists_runE x hd (1/100) (by norm_num), ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    obtain ⟨e0, e1⟩ := (sat_domR _).mp H.end_dom
    have hc := H.const (rightBlock_mem' (fR 1) (Term.const 1) 0) (fun s _ => by
      rw [eval_unit_mul, fE0_eval])
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by rw [hc]; exact hg1.1, e0, e1⟩⟩

end V2VentilatorVcCuffleak
end RelCertifier

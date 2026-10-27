/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
two breath phases and their declared `next` lists), the lowered right guards, and
`ε_r = 0.01` read from the file.

The right model is the breath with a sealed cuff: the breath clock `t` (coordinate 0, `t' = 1`)
and the lung volume `V` (coordinate 1); coordinate 2 is the padding of the bridge's keyed
records (field 0, frozen). Evolve domain: `t ≥ 0`, `−0.4 ≤ V ≤ 0.404`, and the linear face
`V − 0.4 t ≤ 0` (the lung holds no more than the ventilator has delivered).
`INSP` (`t < 1`): `V' = 0.4`; `EXP` (`t ≥ 1`): `V' = −1.923077 V`.
* Existence (i), `INSP`: the linear run `(t₀ + s, V₀ + 0.4 s)`. The flow is TANGENT to the face
  `V − 0.4 t ≤ 0` (`V − 0.4 t` is constant along it), and the cap `V ≤ 0.404` is the face's
  value at the end of a period begun before `t = 1`: `V ≤ 0.4 (t₀ + s) < 0.4 (1 + 0.01) = 0.404`
  for `s ≤ ε_r` (it is approached, never reached, as `t₀ → 1`). `EXP`: the clock and the
  exponential decay of `V` toward 0; `V` stays between `V₀` and 0, so below
  `max V₀ 0 ≤ 0.4 t₀ ≤ 0.4 t`.
* (ii): `INSP` ends in the domain, where `t < 1` is `INSP`'s guard and `t ≥ 1` is `EXP`'s
  (style (b), exit); `EXP`: the clock does not fall (style (a)).
Z3-free; modelled on `MoldingPackCheckring.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.ventilator_vc_cuffleak

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2VentilatorVcCuffleak

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["t", "V"]
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
theorem hp_0_404 : Run.parseRat "0.404" = some ((101:ℚ)/250) := by
  have h : parseQ "0.404" = some (⟨404, 1000⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
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

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) : Term.eval (fR q 0) x = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fI1_eval (x : State (Var 3)) : Term.eval (fR 0 1) x = 2/5 := by
  simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp]

theorem fE1_eval (x : State (Var 3)) : Term.eval (fR 1 1) x = kE * (0 - x (Rv 1)) := by
  simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval, AOp.interp,
    Rv, kE] <;> ring

/-- The padding coordinate 2 (not in `vs`): its right field lowers to 0. -/
theorem fR2_eval (q : ℕ) (hq : q < 2) (x : State (Var 3)) : Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, ventilator_vc_cuffleak_IRv2, vs, Run.dynOf, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ -2/5 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 101/250 ∧
        x (Rv 1) ≤ 2/5 * x (Rv 0)) := by
  simp only [domR, hostEvolve, mR, ventilator_vc_cuffleak_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01, Run.resolveVar, List.findIdx?_cons,
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
      (ν (Rv 0) < 1 ∧ 0 ≤ ν (Rv 0) ∧ -2/5 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 101/250 ∧
        ν (Rv 1) ≤ 2/5 * ν (Rv 0)) := by
  simp [hostGuard, mR, ventilator_vc_cuffleak_IRv2, Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (1 ≤ ν (Rv 0) ∧ 0 ≤ ν (Rv 0) ∧ -2/5 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 101/250 ∧
        ν (Rv 1) ≤ 2/5 * ν (Rv 0)) := by
  simp [hostGuard, mR, ventilator_vc_cuffleak_IRv2, Run.lowerF, Run.lowerE, hp_m0_4, hp_0_0, hp_0_4, hp_0_404, hp_1_0, hp_1_923077, hp_0_01, vs,
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

/-- The run of `INSP` from `x`: the clock and the delivered volume at 0.4 L/s. -/
noncomputable def phiI (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + 1 * t
  else if i.val = 1 then x (Rv 1) + 2/5 * t
  else x (Rv 2)

/-- The run of `EXP` from `x`: the clock and the passive emptying. -/
noncomputable def phiE (x : State (Var 3)) (i : Fin 3) (t : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + 1 * t
  else if i.val = 1 then 0 + (x (Rv 1) - 0) * Real.exp (-(kE * t))
  else x (Rv 2)

theorem phiI_der (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phiI x i) (Term.eval (fR 0 i) (trajRs x (phiI x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval 0 (by norm_num)]
      have hf : phiI x 0 = fun u => x (Rv 0) + 1 * u := by funext u; simp [phiI]
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
      rw [fR0_eval 1 (by norm_num)]
      have hf : phiE x 0 = fun u => x (Rv 0) + 1 * u := by funext u; simp [phiE]
      rw [hf]; exact lin_der _ _ t
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

/-- **`INSP`'s run** from a guard state: tangent to the face `V − 0.4 t ≤ 0`, below the cap
`0.404` for one period. -/
theorem exists_runI (x : State (Var 3)) (hd : Formula.sat domR x) (ht1 : x (Rv 0) < 1) :
    ∃ Φ, ODESol (rightBlock (fR 0) (Term.const 1)) domR x (1/100) Φ := by
  obtain ⟨t0, a0, a1, a2⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phiI x) (1/100) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phiI_der x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => simp [phiI]
    | 1 => simp [phiI]
    | 2 => simp [phiI]
  · rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiI, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_runE (x : State (Var 3)) (hd : Formula.sat domR x) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ Φ, ODESol (rightBlock (fR 1) (Term.const 1)) domR x ε Φ := by
  obtain ⟨t0, a0, a1, a2⟩ := (sat_domR x).mp hd
  have hk : 0 ≤ kE := by unfold kE; norm_num
  refine ⟨_, trajRs_sol x (phiE x) ε hε (fun i => ?_) (fun i t _ _ => phiE_der x i t)
    (fun t ht _ => ?_)⟩
  · match i with
    | 0 => simp [phiE]
    | 1 => simp [phiE]
    | 2 => simp [phiE]
  · obtain ⟨l, u⟩ := exp_approach_between kE 0 (x (Rv 1)) t hk ht
    rw [sat_domR, trajRs_R, trajRs_R]
    simp only [phiE, Fin.isValue, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false]
    have hm : max (x (Rv 1)) 0 ≤ 2/5 * x (Rv 0) := max_le (by linarith) (by linarith)
    refine ⟨by linarith, le_trans (le_min a0 (by norm_num)) l,
      le_trans u (max_le a1 (by norm_num)), by linarith⟩

/-- **Assumption 1 for `ventilator_vc_cuffleak`**, every mode, Z3-free. -/
theorem ventilator_vc_cuffleak_wellFormedR :
    WellFormedR Gr guardR (epsR ventilator_vc_cuffleak_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  interval_cases q
  · -- INSP: the run ends in the domain; `t < 1` is INSP, `t ≥ 1` is EXP
    have hg0 := (sat_guard0 x).mp hg
    refine ⟨exists_runI x hd hg0.1, ?_⟩
    intro t Φ _ H
    obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
    by_cases h1 : Φ t (Rv 0) < 1
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guard0 _).mpr ⟨h1, e0, e1, e2, e3⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, e0, e1, e2, e3⟩⟩
  · -- EXP: the clock does not fall, so `t ≥ 1` is kept
    refine ⟨exists_runE x hd (1/100) (by norm_num), ?_⟩
    intro t Φ _ H
    have hg1 := (sat_guard1 x).mp hg
    obtain ⟨e0, e1, e2, e3⟩ := (sat_domR _).mp H.end_dom
    have hmono := H.mono (rightBlock_mem' (fR 1) (Term.const 1) 0) (fun s _ => by
      rw [eval_unit_mul, fR0_eval 1 (by norm_num)]; norm_num)
    exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
      (sat_guard1 _).mpr ⟨by linarith [hg1.1], e0, e1, e2, e3⟩⟩

end V2VentilatorVcCuffleak
end RelCertifier

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.acc_spoof_limp

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.
The right model (2026-10-30, r10: the `DISENGAGE` hand-back mode and its edges removed) has the
three set-speed modes `NORMAL` / `ECO` / `SPORT` (indices 0, 1, 2), each with guard `20 ≤ v ≤ 40`
and field `v' = (c − v)/2` with `c = 30, 27, 33`; declared edges `NORMAL → NORMAL, ECO, SPORT`,
`ECO → ECO, NORMAL`, `SPORT → SPORT, NORMAL`.
(i) Existence: the explicit exponential toward `c_q ∈ [20, 40]`, staying in the domain `[0, 40]`.
(ii) Style (a), every mode: a contraction toward a set point inside `[20, 40]`, so the guard set
is forward invariant and the self-loop `q → q` is enabled at the end of every run.
Z3-free.
-/
set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AccSpoofLimp

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := acc_spoof_limp_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp270 : Run.parseRat "27.0" = some (27 : ℚ) := by
  have h : parseQ "27.0" = some (⟨270, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp330 : Run.parseRat "33.0" = some (33 : ℚ) := by
  have h : parseQ "33.0" = some (⟨330, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp200 : Run.parseRat "20.0" = some (20 : ℚ) := by
  have h : parseQ "20.0" = some (⟨200, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp400 : Run.parseRat "40.0" = some (40 : ℚ) := by
  have h : parseQ "40.0" = some (⟨400, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
/-- Right fields: `v' = 0.5 (c_q − v)` (`NORMAL` 30, `ECO` 27, `SPORT` 33). -/
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 30 else if q = 1 then 27 else 33

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 1/2 * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp270, hp330, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp270, hp330, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, acc_spoof_limp_IRv2, vs, Run.dynOf, Run.lowerE, hp05, hp300,
      hp270, hp330, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 40) := by
  simp only [domR, hostEvolve, mR, acc_spoof_limp_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp400, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard (`hostGuard` of the
right mode `t`, lowered exactly as the left windows' guards are): the right switches into
`t` only where `t`'s guard holds. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, ECO 1, SPORT 2). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 0), (2, 2), (2, 0)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

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

/-- The right guards, evaluated (`NORMAL`, `ECO`, `SPORT`: `20 ≤ v ≤ 40`). -/
theorem sat_guardR (q : ℕ) (hq : q < 3) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔ 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 40 := by
  interval_cases q <;>
    simp [hostGuard, mR, acc_spoof_limp_IRv2, Run.lowerF, Run.lowerE, hp200, hp400, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR acc_spoof_limp_IRv2 = 1 := by
  simp [epsR, acc_spoof_limp_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem fRo_all (q : ℕ) (hq : q < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ => exact fR1_eval q hq x
  | 2, _ => exact fR2_eval q hq x

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem cRc_mem (q : ℕ) : 20 ≤ cRc q ∧ cRc q ≤ 40 := by
  unfold cRc; split_ifs <;> norm_num

/-- **Assumption 1 for `acc_spoof_limp`**, every mode, Z3-free. -/
theorem acc_spoof_limp_wellFormedR : WellFormedR Gr guardR (epsR acc_spoof_limp_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hc := cRc_mem q
  have hk : (0:ℝ) ≤ 1/2 := by norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (1/2) (cRc q) hk (fR0_eval q hq3)
      (fun i hi s => fRo_all q hq3 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 (by linarith [hc.1])) h1, le_trans h2 (max_le hdx.2 hc.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = 1/2 * (cRc q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq3]
    have hb := H.linear_between (memR q) _ _ hk hf
    -- [20, 40] invariant (set point inside): the self-loop is enabled
    have hgx := (sat_guardR q hq3 x).mp hg
    refine ⟨edgeW q q, edge_mem q q (by interval_cases q <;> decide),
      (sat_guardR q hq3 _).mpr ⟨?_, ?_⟩⟩
    · exact le_trans (le_min hgx.1 hc.1) hb.1
    · exact le_trans hb.2 (max_le hgx.2 hc.2)

end V2AccSpoofLimp
end RelCertifier

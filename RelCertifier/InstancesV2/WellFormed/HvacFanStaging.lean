/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hvac_fan_staging`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three fan speeds, every speed may follow every speed), the lowered right guards, and `ε_r = 1`
read from the file. Dimension 3 (the bridge's default padding for a one-variable file, as for
the literature benchmarks: coordinate 0 is the zone temperature `T`, 1 and 2 are frozen).

Every speed is a contraction `T' = 0.05 (c − T)` inside the zone's range `[16, 32]` (`LOW`
toward 27, `MED` toward 24, `HIGH` toward 21).
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (b) for every mode: a run ends in the evolve domain `[16, 32]`, which is `MED`'s
  guard, and `MED` is a declared successor of every speed.
Z3-free; modelled on `TankDos3to1.lean`.
-/
import RelCertifier.InstancesV2.BenchIR.hvac_fan_staging
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2HvacFanStaging

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["T"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := hvac_fan_staging_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp27 : Run.parseRat "27.0" = some (27 : ℚ) := by
  have h : parseQ "27.0" = some (⟨270, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp24 : Run.parseRat "24.0" = some (24 : ℚ) := by
  have h : parseQ "24.0" = some (⟨240, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp21 : Run.parseRat "21.0" = some (21 : ℚ) := by
  have h : parseQ "21.0" = some (⟨210, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp16 : Run.parseRat "16.0" = some (16 : ℚ) := by
  have h : parseQ "16.0" = some (⟨160, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp32 : Run.parseRat "32.0" = some (32 : ℚ) := by
  have h : parseQ "32.0" = some (⟨320, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- Right fields: `T' = 0.05 (c_q − T)` (`LOW` 27, `MED` 24, `HIGH` 21). -/
noncomputable def kR (_q : ℕ) : ℝ := 1/20
noncomputable def cRc (q : ℕ) : ℝ := if q = 0 then 27 else if q = 1 then 24 else 21

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, hvac_fan_staging_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp27, hp24,
      hp21, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cRc]

theorem fRo_eval (q : ℕ) (hq : q < 3) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | ⟨1, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, hvac_fan_staging_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp27,
        hp24, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]
  | ⟨2, _⟩, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, hvac_fan_staging_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp27,
        hp24, hp21, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (16 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 32) := by
  simp only [domR, hostEvolve, mR, hvac_fan_staging_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp16, hp32, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (LOW 0, MED 1, HIGH 2): every speed may follow every
speed. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

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

/-- `MED`'s guard, evaluated: the whole range `[16, 32]`. -/
theorem sat_guardMED (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ (16 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 32) := by
  simp [hostGuard, mR, hvac_fan_staging_IRv2, Run.lowerF, Run.lowerE, hp16, hp32, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: every speed is a contraction inside `[16, 32]` -/

theorem hwfB (q : ℕ) (hq : q < 3) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const 1) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 16 32) ?_ ?_ ?_
  · intro i x
    by_cases hi : i = 0
    · subst hi
      simp only [Term.eval, AOp.interp, contractF, if_true]
      rw [fR0_eval q hq]
    · simp only [Term.eval, AOp.interp, contractF, if_neg hi]
      rw [fRo_eval q hq i hi]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (kR q) (cRc q) 16 32 dt ?_ ?_ ?_
    · unfold kR; norm_num
    · unfold cRc; split_ifs <;> norm_num
    · unfold cRc; split_ifs <;> norm_num

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR hvac_fan_staging_IRv2 = 1 := by
  simp [epsR, hvac_fan_staging_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- **Assumption 1 for `hvac_fan_staging`**, every mode, Z3-free. -/
theorem hvac_fan_staging_wellFormedR : WellFormedR Gr guardR (epsR hvac_fan_staging_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_of_wellFormedFlowB (by norm_num) (hwfB q hq3 1) hd, ?_⟩
  intro t Φ _ H
  -- the run ends in the evolve domain `[16, 32]`, which is `MED`'s guard
  have he := (sat_domR _).mp H.end_dom
  refine ⟨edgeW q 1, edge_mem q 1 (by interval_cases q <;> decide), ?_⟩
  exact (sat_guardMED _).mpr he

end V2HvacFanStaging
end RelCertifier

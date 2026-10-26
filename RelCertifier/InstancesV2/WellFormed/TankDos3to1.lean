/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
one mode and its self-loop), the lowered right guard, and `ε_r = 1` read from the file.

The nominal loop `MODULATE` is the contraction `h' = 0.2 (1.0 − h)` on the valve's unsaturated
range `[0.4, 2.0]` (its guard and its evolve domain).
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (a): the range is forward invariant (1.0 approached from either side), so every
  run ends in the guard and the self-loop is enabled.
Z3-free; modelled on `WatertankTwospeed.lean`.
-/
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2TankDos3to1

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["h"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := tank_dos_3to1_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp04 : Run.parseRat "0.4" = some ((2:ℚ)/5) := by
  have h : parseQ "0.4" = some (⟨4, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- The right field: `h' = 0.2 (1.0 − h)`. -/
noncomputable def kR : ℝ := 1/5
noncomputable def cRc : ℝ := 1

theorem fR0_eval (x : State (Var 2)) :
    Term.eval (fR 0 0) x = kR * (cRc - x (Rv 0)) := by
  simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp02, hp10,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (x : State (Var 2)) :
    Term.eval (fR 0 1) x = 0 := by
  simp [fR, hostDyn, mR, tank_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp02, hp10,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (2/5 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 2) := by
  simp only [domR, hostEvolve, mR, tank_dos_3to1_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp04, hp20, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's mode and its declared self-loop) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (MODULATE 0). -/
def edgeList : List (ℕ × ℕ) := [(0, 0)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 1) : Gr.modeAt q = some (modeW q) := by
  interval_cases q; rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q = 0 ∧ m = modeW 0 := by
  match q with
  | 0 => exact ⟨rfl, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 1 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guard, evaluated (`0.4 ≤ h ≤ 2.0`). -/
theorem sat_guardR (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ (2/5 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 2) := by
  simp [hostGuard, mR, tank_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp04, hp20, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem edge_mem : edgeW 0 0 ∈ Gr.edgesFrom 0 :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(0, 0), by decide, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: the mode is a contraction toward 1.0 inside `[0.4, 2.0]` -/

theorem hwfB (dt : ℝ) : WellFormedFlowB (fR 0) (Term.const 1) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 kR cRc)
    (lam := Term.const 1) (domR := bandDom 0 (2/5) 2) ?_ ?_ ?_
  · intro i x
    match i with
    | 0 =>
        simp only [Term.eval, AOp.interp, contractF, if_true]
        rw [fR0_eval]
    | 1 =>
        simp only [Term.eval, AOp.interp, contractF]
        rw [fR1_eval]
        simp [Term.eval]
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 kR cRc (2/5) 2 dt ?_ ?_ ?_
    · unfold kR; norm_num
    · unfold cRc; norm_num
    · unfold cRc; norm_num

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR tank_dos_3to1_IRv2 = 1 := by
  simp [epsR, tank_dos_3to1_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fieldR (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) s = kR * (cRc - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval]

theorem memR : (Rv 0, Term.binop .mul (Term.const 1) (fR 0 0)) ∈ (modeW 0).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `tank_dos_3to1`**, Z3-free. -/
theorem tank_dos_3to1_wellFormedR : WellFormedR Gr guardR (epsR tank_dos_3to1_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨rfl, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR x).mp hg
  refine ⟨?_, ?_⟩
  · exact exists_of_wellFormedFlowB (by norm_num) (hwfB 1) hd
  · intro t Φ _ H
    have hk : 0 ≤ kR := by unfold kR; norm_num
    have hf : ∀ s, Formula.sat (modeW 0).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR 0 0)) s = kR * (cRc - s (Rv 0)) :=
      fun s _ => fieldR s
    refine ⟨edgeW 0 0, edge_mem, (sat_guardR _).mpr ?_⟩
    by_cases hx : x (Rv 0) ≤ 1
    · have hup := H.linear_up memR _ _ hk hf (by simp only [cRc]; exact hx)
      simp only [cRc] at hup
      exact ⟨by linarith [hup.1], by linarith [hup.2]⟩
    · replace hx := le_of_lt (not_le.mp hx)
      have hdn := H.linear_down memR _ _ hk hf (by simp only [cRc]; exact hx)
      simp only [cRc] at hdn
      exact ⟨by linarith [hdn.1], by linarith [hdn.2]⟩

end V2TankDos3to1
end RelCertifier

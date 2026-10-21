/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant and of the stretches: over the right
automaton `Gr` of the Theorem 3 instance (`InstancesV2/Modal/WatertankTwospeed.lean`), the
lowered right guards, and `ε_r = 1` read from the file.

Both modes are contractions `x' = k (12.5 − x)` (`Fast` 0.6, `Slow` 0.2) inside the tank `[0, 25]`.
* Existence (i): the explicit exponential (`hwfB`, unit stretch).
* (ii), style (b) for `Fast` (`[2, 8)`): a run ends in `[x₀, 12.5)`, inside `Fast` or `Slow`
  (`x ≥ 8`); style (a) for `Slow`: `x ≥ 8` is forward invariant (12.5 approached from either
  side, the run stays above 8), the self-loop is enabled.
Z3-free.
-/
import RelCertifier.InstancesV2.BenchIR.watertank_twospeed
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace V2WatertankTwospeed

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := watertank_twospeed_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp125 : Run.parseRat "12.5" = some ((25:ℚ)/2) := by
  have h : parseQ "12.5" = some (⟨125, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp20 : Run.parseRat "2.0" = some (2 : ℚ) := by
  have h : parseQ "2.0" = some (⟨20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp80 : Run.parseRat "8.0" = some (8 : ℚ) := by
  have h : parseQ "8.0" = some (⟨80, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
/-- Right fields: `x' = k_q (12.5 − x)` (`Fast` 0.6, `Slow` 0.2). -/
noncomputable def kR (q : ℕ) : ℝ := if q = 0 then 3/5 else 1/5
noncomputable def cRc (_q : ℕ) : ℝ := 25/2

theorem fR0_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = kR q * (cRc q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_twospeed_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp02,
      hp125, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, kR, cRc]

theorem fR1_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, watertank_twospeed_IRv2, vs, Run.dynOf, Run.lowerE, hp06, hp02,
      hp125, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 25) := by
  simp only [domR, hostEvolve, mR, watertank_twospeed_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp250, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (Fast 0, Slow 1). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 1)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 2) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 2 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 2 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The right guards, evaluated (Fast `[2, 8)`, Slow `x ≥ 8`). -/
theorem sat_guardR (q : ℕ) (hq : q < 2) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 8 else 8 ≤ ν (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mR, watertank_twospeed_IRv2, Run.lowerF, Run.lowerE, hp20, hp80, vs,
      Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem hlt : ∀ q, ∀ e ∈ Gr.edgesFrom q, e.tgt < Gr.modes.length := by
  intro q e he
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [edgeW, Gr]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The stretch of each pairing (the emitted cover's λ per right mode) -/

/-- `Fast` at stretch 1 (the same gain as the attacked pump), `Slow` at stretch 31/10 (the
first grid point from the gain ratio 3). One left window, two stretches: the per-pairing
fallback's exhibit. -/
noncomputable def lam (_l q : ℕ) : ℝ := if q = 0 then 1 else 31/10

/-! ## Existence: every right mode is a contraction toward 12.5 inside `[0, 25]` -/

/-- Existence at any nonnegative stretch (the pairings' stretches differ, and Assumption 1
needs the unit one). -/
theorem hwfB' (q : ℕ) (hq : q < 2) (lamv : ℝ) (hlv : 0 ≤ lamv) (dt : ℝ) :
    WellFormedFlowB (fR q) (Term.const lamv) domR dt := by
  refine WellFormedFlowB_transfer (fR := contractF 0 (lamv * kR q) (cRc q))
    (lam := Term.const 1) (domR := bandDom 0 0 25) ?_ ?_ ?_
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
  · intro x
    rw [sat_domR]
    simp [bandDom, Formula.sat, CompOp.interp, Term.eval]
  · refine WellFormedFlowB_contract 0 (lamv * kR q) (cRc q) 0 25 dt ?_ ?_ ?_
    · exact mul_nonneg hlv (by unfold kR; split_ifs <;> norm_num)
    · unfold cRc; norm_num
    · unfold cRc; norm_num


theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR watertank_twospeed_IRv2 = 1 := by
  simp [epsR, watertank_twospeed_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fieldR (q : ℕ) (hq : q < 2) (s : State (Var 2)) :
    Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) := by
  rw [eval_unit_mul, fR0_eval q hq]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `watertank_twospeed`**, every mode, Z3-free. -/
theorem watertank_twospeed_wellFormedR : WellFormedR Gr guardR (epsR watertank_twospeed_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq2, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq2 x).mp hg
  refine ⟨?_, ?_⟩
  · exact exists_of_wellFormedFlowB (by norm_num) (hwfB' q hq2 1 zero_le_one 1) hd
  · intro t Φ _ H
    have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => fieldR q hq2 s
    have pick : ∀ t', (q, t') ∈ edgeList → t' < 2 →
        Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
        ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
      fun t' he _ hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
    interval_cases q
    · -- Fast: a run ends in [x₀, 12.5), inside Fast or Slow
      simp only [if_true] at hgx
      have hup := H.linear_up (memR 0) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
      have hlt := H.linear_lt (memR 0) _ _ hf (by simp only [cRc]; norm_num; linarith)
      simp only [cRc] at hup hlt; norm_num at hup hlt
      by_cases h8 : Φ t (Rv 0) < 8
      · exact pick 0 (by decide) (by norm_num) ((sat_guardR 0 (by norm_num) _).mpr
          (by simp only [if_true]; exact ⟨by linarith, h8⟩))
      · exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith))
    · -- Slow: x ≥ 8 is invariant (12.5 approached from below or above)
      norm_num at hgx
      by_cases hx : x (Rv 0) ≤ 25/2
      · have hup := H.linear_up (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
        simp only [cRc] at hup; norm_num at hup
        exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith))
      · replace hx := le_of_lt (not_le.mp hx)
        have hdn := H.linear_down (memR 1) _ _ hk hf (by simp only [cRc]; norm_num; linarith)
        simp only [cRc] at hdn; norm_num at hdn
        exact pick 1 (by decide) (by norm_num) ((sat_guardR 1 (by norm_num) _).mpr
          (by norm_num; linarith [hdn.1]))

end V2WatertankTwospeed
end RelCertifier

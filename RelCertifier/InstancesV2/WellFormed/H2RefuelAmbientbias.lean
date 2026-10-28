import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.h2_refuel_ambientbias

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's six modes and their declared
`next` lists), the lowered right guards, and `ε_r = 1` read from the file. The right model is
the staged pressure-ramp fill with the correct ambient reading (end pressure `70.0 MPa`):
every stage is a 1-D contraction `p' = k (c − p)` inside the evolve domain `[0, 87.5]`:
`STAGE1` (`[0.5, 18)`, `k = 0.05`, `c = 20`), `STAGE2` (`[18, 38)`, `0.05`, `40`),
`STAGE3` (`[38, 58)`, `0.05`, `60`), `TOPOFF` (`[58, 70)`, `0.05`, `70.5`); `COMPLETE`
(`p ≥ 70`) and `ABORT` (`p < 0.5`) hold the pressure (`p' = 0`, read as `k = 0`).
* Existence (i): the explicit exponential (`exists_contract_run`); every set point lies in
  `[0, 87.5]` (for the two held modes the set point is taken as 70 and 0).
* (ii): a run stays between its start and its set point (`linear_between`), so
  `STAGE1` ends in `[0.5, 20] ⊆ STAGE1 ∪ STAGE2`, `STAGE2` in `[18, 40] ⊆ STAGE2 ∪ STAGE3`,
  `STAGE3` in `[38, 60] ⊆ STAGE3 ∪ TOPOFF`, `TOPOFF` in `[58, 70.5] ⊆ TOPOFF ∪ COMPLETE`
  (style (b), exits), `COMPLETE` in `[70, 87.5]` and `ABORT` in `[0, 0.5)` (style (a),
  invariant); each entered mode is a declared successor.
Z3-free; modelled on `EngineStartHighidle.lean`.
-/
namespace RelCertifier
namespace V2H2RefuelAmbientbias

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["p"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := h2_refuel_ambientbias_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp005 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp20 : Run.parseRat "20" = some (20 : ℚ) := by
  have h : parseQ "20" = some (⟨20, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp40 : Run.parseRat "40" = some (40 : ℚ) := by
  have h : parseQ "40" = some (⟨40, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp60 : Run.parseRat "60" = some (60 : ℚ) := by
  have h : parseQ "60" = some (⟨60, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp705 : Run.parseRat "70.5" = some ((141:ℚ)/2) := by
  have h : parseQ "70.5" = some (⟨705, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp180 : Run.parseRat "18.0" = some (18 : ℚ) := by
  have h : parseQ "18.0" = some (⟨180, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp380 : Run.parseRat "38.0" = some (38 : ℚ) := by
  have h : parseQ "38.0" = some (⟨380, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp580 : Run.parseRat "58.0" = some (58 : ℚ) := by
  have h : parseQ "58.0" = some (⟨580, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp700 : Run.parseRat "70.0" = some (70 : ℚ) := by
  have h : parseQ "70.0" = some (⟨700, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp875 : Run.parseRat "87.5" = some ((175:ℚ)/2) := by
  have h : parseQ "87.5" = some (⟨875, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-- Right fields: `p' = k_q (c_q − p)` (`STAGE1` 0.05/20, `STAGE2` 0.05/40, `STAGE3` 0.05/60,
`TOPOFF` 0.05/70.5; `COMPLETE` and `ABORT` are written `0.0` in the file, read as `k = 0`
with the set points 70 and 0). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 1/20 else if q = 1 then 1/20 else if q = 2 then 1/20 else if q = 3 then 1/20
  else 0
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 20 else if q = 1 then 40 else if q = 2 then 60 else if q = 3 then 141/2
  else if q = 4 then 70 else 0

theorem fR0_eval (q : ℕ) (hq : q < 6) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, h2_refuel_ambientbias_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp20,
      hp40, hp60, hp705, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cR]

theorem fRo_eval (q : ℕ) (hq : q < 6) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, h2_refuel_ambientbias_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp20,
        hp40, hp60, hp705, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval]
  | 2, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, h2_refuel_ambientbias_IRv2, vs, Run.dynOf, Run.lowerE, hp005, hp20,
        hp40, hp60, hp705, hp00, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 175 / 2) := by
  simp only [domR, hostEvolve, mR, h2_refuel_ambientbias_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp875, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (STAGE1 0, STAGE2 1, STAGE3 2, TOPOFF 3, COMPLETE 4,
ABORT 5). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 5), (1, 1), (1, 2), (1, 5), (2, 2), (2, 3), (3, 3), (3, 4), (4, 4),
   (5, 5)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4, modeW 5]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 6) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 6 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 5 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 6 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ 1 / 2 ≤ ν (Rv 0) ∧ ν (Rv 0) < 18 := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp05, hp180, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ 18 ≤ ν (Rv 0) ∧ ν (Rv 0) < 38 := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp180, hp380, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ 38 ≤ ν (Rv 0) ∧ ν (Rv 0) < 58 := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp380, hp580, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ 58 ≤ ν (Rv 0) ∧ ν (Rv 0) < 70 := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp580, hp700, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔ 70 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp700, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g5 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 5)) ν ↔ ν (Rv 0) < 1 / 2 := by
  simp [hostGuard, mR, h2_refuel_ambientbias_IRv2, Run.lowerF, Run.lowerE, hp05, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR h2_refuel_ambientbias_IRv2 = 1 := by
  simp [epsR, h2_refuel_ambientbias_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- A coordinate between `a` and `c` lies in any interval containing both. -/
theorem between_bounds {a c y lo hi : ℝ} (hb : min a c ≤ y ∧ y ≤ max a c) (h1 : lo ≤ a)
    (h2 : lo ≤ c) (h3 : a ≤ hi) (h4 : c ≤ hi) : lo ≤ y ∧ y ≤ hi :=
  ⟨le_trans (le_min h1 h2) hb.1, le_trans hb.2 (max_le h3 h4)⟩

/-- **Assumption 1 for `h2_refuel_ambientbias`**, every mode, Z3-free. -/
theorem h2_refuel_ambientbias_wellFormedR :
    WellFormedR Gr guardR (epsR h2_refuel_ambientbias_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq6, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  have hcr : 0 ≤ cR q ∧ cR q ≤ 175 / 2 := by unfold cR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq6)
      (fun i hi s => fRo_eval q hq6 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cR q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq6]
    have hb := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- STAGE1: rises toward 20, ends in [0.5, 20]: STAGE1 below 18, STAGE2 from 18
      have hgx := (sat_g0 x).mp hg
      rw [show cR 0 = 20 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (20:ℝ))
      by_cases h18 : Φ t (Rv 0) < 18
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨hy.1, h18⟩⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_g1 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
    · -- STAGE2: rises toward 40, ends in [18, 40]: STAGE2 below 38, STAGE3 from 38
      have hgx := (sat_g1 x).mp hg
      rw [show cR 1 = 40 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (40:ℝ))
      by_cases h38 : Φ t (Rv 0) < 38
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨hy.1, h38⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
          (sat_g2 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
    · -- STAGE3: rises toward 60, ends in [38, 60]: STAGE3 below 58, TOPOFF from 58
      have hgx := (sat_g2 x).mp hg
      rw [show cR 2 = 60 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (60:ℝ))
      by_cases h58 : Φ t (Rv 0) < 58
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr ⟨hy.1, h58⟩⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide),
          (sat_g3 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
    · -- TOPOFF: rises toward 70.5, ends in [58, 70.5]: TOPOFF below 70, COMPLETE from 70
      have hgx := (sat_g3 x).mp hg
      rw [show cR 3 = 141 / 2 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2])
        (le_refl ((141:ℝ) / 2))
      by_cases h70 : Φ t (Rv 0) < 70
      · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_g3 _).mpr ⟨hy.1, h70⟩⟩
      · exact ⟨edgeW 3 4, edge_mem 3 4 (by decide), (sat_g4 _).mpr (by linarith)⟩
    · -- COMPLETE: held (k = 0) from p ≥ 70, so the run stays at or above 70 (invariant)
      have hgx := (sat_g4 x).mp hg
      rw [show cR 4 = 70 by norm_num [cR]] at hb
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide),
        (sat_g4 _).mpr (le_trans (le_min hgx (by norm_num)) hb.1)⟩
    · -- ABORT: held (k = 0) from p < 0.5, so the run stays below 0.5 (invariant)
      have hgx := (sat_g5 x).mp hg
      rw [show cR 5 = 0 by norm_num [cR]] at hb
      exact ⟨edgeW 5 5, edge_mem 5 5 (by decide),
        (sat_g5 _).mpr (lt_of_le_of_lt hb.2 (max_lt hgx (by norm_num)))⟩

end V2H2RefuelAmbientbias
end RelCertifier

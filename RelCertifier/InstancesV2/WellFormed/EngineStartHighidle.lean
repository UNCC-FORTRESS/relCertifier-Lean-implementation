import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.engine_start_highidle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle`: Assumption 1 of the right model (`WellFormedR`)

Over the instance's guarded right automaton `Gr` (the file's five modes and their declared
`next` lists), the lowered right guards, and `ε_r = 1` read from the file. The right model is
the ground-idle start schedule (idle `62 %`): every mode is a 1-D contraction
`n' = k (c − n)` inside the evolve domain `[0, 110]`:
`STARTER` (`[5, 25)`, `k = 0.1`, `c = 30`), `LIGHTOFF` (`[25, 50)`, `0.08`, `55`),
`SELF` (`[50, 60)`, `0.15`, `62`), `IDLE` (`n ≥ 60`, `0.5`, `62`), `ABORT` (`n < 5`, `0.2`, `0`).
* Existence (i): the explicit exponential (`exists_contract_run`); every set point lies in
  `[0, 110]`.
* (ii): a run stays between its start and its set point (`linear_between`), so
  `STARTER` ends in `[5, 30] ⊆ STARTER ∪ LIGHTOFF`, `LIGHTOFF` in `[25, 55] ⊆ LIGHTOFF ∪ SELF`,
  `SELF` in `[50, 62] ⊆ SELF ∪ IDLE` (style (b), exits), `IDLE` in `[60, 110]` and `ABORT` in
  `[0, 5)` (style (a), invariant); each entered mode is a declared successor.
Z3-free; modelled on `TankDos3to1.lean` and `AccSpoofLimp.lean`.
-/
namespace RelCertifier
namespace V2EngineStartHighidle

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["n"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := engine_start_highidle_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp008 : Run.parseRat "0.08" = some ((2:ℚ)/25) := by
  have h : parseQ "0.08" = some (⟨8, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp015 : Run.parseRat "0.15" = some ((3:ℚ)/20) := by
  have h : parseQ "0.15" = some (⟨15, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp05 : Run.parseRat "0.5" = some ((1:ℚ)/2) := by
  have h : parseQ "0.5" = some (⟨5, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp02 : Run.parseRat "0.2" = some ((1:ℚ)/5) := by
  have h : parseQ "0.2" = some (⟨2, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp55 : Run.parseRat "55" = some (55 : ℚ) := by
  have h : parseQ "55" = some (⟨55, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp62 : Run.parseRat "62" = some (62 : ℚ) := by
  have h : parseQ "62" = some (⟨62, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp250 : Run.parseRat "25.0" = some (25 : ℚ) := by
  have h : parseQ "25.0" = some (⟨250, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp500 : Run.parseRat "50.0" = some (50 : ℚ) := by
  have h : parseQ "50.0" = some (⟨500, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp600 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp1100 : Run.parseRat "110.0" = some (110 : ℚ) := by
  have h : parseQ "110.0" = some (⟨1100, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-- Right fields: `n' = k_q (c_q − n)` (`STARTER` 0.1/30, `LIGHTOFF` 0.08/55, `SELF` 0.15/62,
`IDLE` 0.5/62, `ABORT` 0.2/0, the last written `−0.2 n` in the file). -/
noncomputable def kR (q : ℕ) : ℝ :=
  if q = 0 then 1/10 else if q = 1 then 2/25 else if q = 2 then 3/20 else if q = 3 then 1/2
  else 1/5
noncomputable def cR (q : ℕ) : ℝ :=
  if q = 0 then 30 else if q = 1 then 55 else if q = 2 then 62 else if q = 3 then 62 else 0

theorem fR0_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) :
    Term.eval (fR q 0) x = kR q * (cR q - x (Rv 0)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
      hp015, hp05, hp02, hp30, hp55, hp62, Run.resolveVar, List.findIdx?_cons, List.finRange,
      ITerm.toHost, Term.eval, AOp.interp, Rv, kR, cR]

theorem fRo_eval (q : ℕ) (hq : q < 5) (i : Fin 3) (hi : i ≠ 0) (x : State (Var 3)) :
    Term.eval (fR q i) x = 0 := by
  match i, hi with
  | 1, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
        hp015, hp05, hp02, hp30, hp55, hp62, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval]
  | 2, _ =>
    interval_cases q <;>
      simp [fR, hostDyn, mR, engine_start_highidle_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp008,
        hp015, hp05, hp02, hp30, hp55, hp62, Run.resolveVar, List.findIdx?_cons, List.finRange,
        ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 110) := by
  simp only [domR, hostEvolve, mR, engine_start_highidle_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp1100, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (STARTER 0, LIGHTOFF 1, SELF 2, IDLE 3, ABORT 4). -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 4), (1, 1), (1, 2), (1, 4), (2, 2), (2, 3), (3, 3), (4, 4)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

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

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## The right guards, evaluated -/

theorem sat_g0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔ 5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 25 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp50, hp250, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔ 25 ≤ ν (Rv 0) ∧ ν (Rv 0) < 50 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp250, hp500, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ 50 ≤ ν (Rv 0) ∧ ν (Rv 0) < 60 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp500, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g3 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 3)) ν ↔ 60 ≤ ν (Rv 0) := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp600, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem sat_g4 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 4)) ν ↔ ν (Rv 0) < 5 := by
  simp [hostGuard, mR, engine_start_highidle_IRv2, Run.lowerF, Run.lowerE, hp50, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR engine_start_highidle_IRv2 = 1 := by
  simp [epsR, engine_start_highidle_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- A coordinate between `a` and `c` lies in any interval containing both. -/
theorem between_bounds {a c y lo hi : ℝ} (hb : min a c ≤ y ∧ y ≤ max a c) (h1 : lo ≤ a)
    (h2 : lo ≤ c) (h3 : a ≤ hi) (h4 : c ≤ hi) : lo ≤ y ∧ y ≤ hi :=
  ⟨le_trans (le_min h1 h2) hb.1, le_trans hb.2 (max_le h3 h4)⟩

/-- **Assumption 1 for `engine_start_highidle`**, every mode, Z3-free. -/
theorem engine_start_highidle_wellFormedR :
    WellFormedR Gr guardR (epsR engine_start_highidle_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  have hcr : 0 ≤ cR q ∧ cR q ≤ 110 := by unfold cR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cR q) hk (fR0_eval q hq5)
      (fun i hi s => fRo_eval q hq5 i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 hcr.1) h1, le_trans h2 (max_le hdx.2 hcr.2)⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cR q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq5]
    have hb := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- STARTER: rises toward 30, ends in [5, 30]: STARTER below 25, LIGHTOFF from 25
      have hgx := (sat_g0 x).mp hg
      rw [show cR 0 = 30 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (30:ℝ))
      by_cases h25 : Φ t (Rv 0) < 25
      · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_g0 _).mpr ⟨hy.1, h25⟩⟩
      · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
          (sat_g1 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
    · -- LIGHTOFF: rises toward 55, ends in [25, 55]: LIGHTOFF below 50, SELF from 50
      have hgx := (sat_g1 x).mp hg
      rw [show cR 1 = 55 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (55:ℝ))
      by_cases h50 : Φ t (Rv 0) < 50
      · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_g1 _).mpr ⟨hy.1, h50⟩⟩
      · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
          (sat_g2 _).mpr ⟨by linarith, by linarith [hy.2]⟩⟩
    · -- SELF: rises toward 62, ends in [50, 62]: SELF below 60, IDLE from 60
      have hgx := (sat_g2 x).mp hg
      rw [show cR 2 = 62 by norm_num [cR]] at hb
      have hy := between_bounds hb hgx.1 (by norm_num) (by linarith [hgx.2]) (le_refl (62:ℝ))
      by_cases h60 : Φ t (Rv 0) < 60
      · exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_g2 _).mpr ⟨hy.1, h60⟩⟩
      · exact ⟨edgeW 2 3, edge_mem 2 3 (by decide), (sat_g3 _).mpr (by linarith)⟩
    · -- IDLE: contracts toward 62 from n ≥ 60, so the run stays at or above 60 (invariant)
      have hgx := (sat_g3 x).mp hg
      rw [show cR 3 = 62 by norm_num [cR]] at hb
      exact ⟨edgeW 3 3, edge_mem 3 3 (by decide),
        (sat_g3 _).mpr (le_trans (le_min hgx (by norm_num)) hb.1)⟩
    · -- ABORT: decays toward 0 from n < 5, so the run stays below 5 (invariant)
      have hgx := (sat_g4 x).mp hg
      rw [show cR 4 = 0 by norm_num [cR]] at hb
      exact ⟨edgeW 4 4, edge_mem 4 4 (by decide),
        (sat_g4 _).mpr (lt_of_le_of_lt hb.2 (max_lt hgx (by norm_num)))⟩

end V2EngineStartHighidle
end RelCertifier


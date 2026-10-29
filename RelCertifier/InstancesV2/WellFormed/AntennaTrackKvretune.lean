/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `antenna_track_kvretune`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three modes `TRACK`, `STOW`, `STOWED` and their declared `next` lists), the lowered right
guards, and `ε_r = 0.05` read from the file.

The right model is the elevation axis as commissioned: the pass clock `t` (coordinate 0), the
commanded elevation `c` (coordinate 1) and the actual elevation `x` (coordinate 2), inside
`0 ≤ t`, `-2 ≤ c, x ≤ 92`. Every mode has `t' = 1` and the position loop `x' = 30 (c − x)`;
the command rate is `-0.7` (`TRACK`), `5` (`STOW`), `0` (`STOWED`). Guards (each with the
domain): `TRACK` `t < 60 ∧ 46.95 ≤ c + 0.7 t ≤ 47.05`, `STOW` `60 ≤ t ∧ c < 90`, `STOWED`
`60 ≤ t ∧ 90 ≤ c`.
* Existence (i): the explicit run `t₀ + s`, `c₀ + r s` and `x` the variation-of-constants
  solution forced by `30 c(s)` (`forcedSol`), which stays in `[min x₀ (-2), max x₀ 92]`
  (`forcedSol_between`) as long as `c` stays in `[-2, 92]` over the control interval: in
  `TRACK` the band gives `c₀ > 4.95`, so `c ≥ 4.9` over `0.05 s`; in `STOW` `c₀ < 90` rises by
  at most `0.25`; in `STOWED` `c` is frozen.
* (ii): `t` and `c` are affine along every run (`rate_le`/`rate_ge`). `TRACK` keeps
  `c + 0.7 t`, so it ends in `TRACK` (below 60) or in `STOW` (from 60, with `c ≤ 47.05 < 90`);
  `STOW` keeps `60 ≤ t` and ends in `STOW` (`c < 90`) or `STOWED` (`90 ≤ c`); `STOWED` is
  invariant.
Z3-free; modelled on `FurnaceProgramTimebase.lean` and `RoverTerrain2to4.lean`.
-/

import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.WellFormedTerrain
import RelCertifier.InstancesV2.BenchIR.antenna_track_kvretune

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2AntennaTrackKvretune

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["t", "c", "x"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := antenna_track_kvretune_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp_1_0 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m0_7 : Run.parseRat "-0.7" = some (-(7:ℚ)/10) := by
  have h : parseQ "-0.7" = some (⟨-7, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp_30 : Run.parseRat "30" = some (30 : ℚ) := by
  have h : parseQ "30" = some (⟨30, 1⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_5_0 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_0 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_60_0 : Run.parseRat "60.0" = some (60 : ℚ) := by
  have h : parseQ "60.0" = some (⟨600, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_7 : Run.parseRat "0.7" = some ((7:ℚ)/10) := by
  have h : parseQ "0.7" = some (⟨7, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_46_95 : Run.parseRat "46.95" = some ((939:ℚ)/20) := by
  have h : parseQ "46.95" = some (⟨4695, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_47_05 : Run.parseRat "47.05" = some ((941:ℚ)/20) := by
  have h : parseQ "47.05" = some (⟨4705, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_m2_0 : Run.parseRat "-2.0" = some (-2 : ℚ) := by
  have h : parseQ "-2.0" = some (⟨-20, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp_92_0 : Run.parseRat "92.0" = some (92 : ℚ) := by
  have h : parseQ "92.0" = some (⟨920, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_90_0 : Run.parseRat "90.0" = some (90 : ℚ) := by
  have h : parseQ "90.0" = some (⟨900, 10⟩ : QF) := by decide
  norm_num [Run.parseRat, h]
theorem hp_0_05 : Run.parseRat "0.05" = some ((1:ℚ)/20) := by
  have h : parseQ "0.05" = some (⟨5, 100⟩ : QF) := by decide
  norm_num [Run.parseRat, h]

/-! ## The right fields, domain and guards, evaluated -/

/-- Command rates: `TRACK` `-0.7`, `STOW` `5`, `STOWED` `0`. -/
noncomputable def rate (q : ℕ) : ℝ := if q = 0 then -7/10 else if q = 1 then 5 else 0

theorem rate0 : rate 0 = -7/10 := by norm_num [rate]
theorem rate1 : rate 1 = 5 := by norm_num [rate]
theorem rate2 : rate 2 = 0 := by norm_num [rate]

theorem fR0_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 0) x = 1 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, antenna_track_kvretune_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0,
      hp_m0_7, hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0,
      hp_90_0, hp_0_05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 1) x = rate q := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, antenna_track_kvretune_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0,
      hp_m0_7, hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0,
      hp_90_0, hp_0_05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv, rate]

theorem fR2_eval (q : ℕ) (hq : q < 3) (x : State (Var 3)) :
    Term.eval (fR q 2) x = 30 * (x (Rv 1) - x (Rv 2)) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, antenna_track_kvretune_IRv2, vs, Run.dynOf, Run.lowerE, hp_1_0,
      hp_m0_7, hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0,
      hp_90_0, hp_0_05, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔
      (0 ≤ x (Rv 0) ∧ -2 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 92 ∧ -2 ≤ x (Rv 2) ∧ x (Rv 2) ≤ 92) := by
  simp only [domR, hostEvolve, mR, antenna_track_kvretune_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp_1_0, hp_m0_7, hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7,
    hp_46_95, hp_47_05, hp_m2_0, hp_92_0, hp_90_0, hp_0_05, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (TRACK 0, STOW 1, STOWED 2). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

noncomputable def Gr : SearchGraph (Var 3) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 3)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  have hlen : q < 3 := by
    by_contra h
    have hn : Gr.modeAt q = none :=
      List.getElem?_eq_none (by show 3 ≤ q; omega)
    rw [hn] at hm; cases hm
  refine ⟨hlen, ?_⟩
  rw [Gr_modeAt q hlen] at hm
  exact (Option.some.inj hm).symm

theorem sat_guard0 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 0)) ν ↔
      (ν (Rv 0) < 60 ∧ 939/20 ≤ ν (Rv 1) + 7/10 * ν (Rv 0) ∧
        ν (Rv 1) + 7/10 * ν (Rv 0) ≤ 941/20 ∧ 0 ≤ ν (Rv 0) ∧ -2 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 92 ∧
        -2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 92) := by
  simp [hostGuard, mR, antenna_track_kvretune_IRv2, Run.lowerF, Run.lowerE, hp_1_0, hp_m0_7,
    hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0, hp_90_0,
    hp_0_05, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard1 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 1)) ν ↔
      (60 ≤ ν (Rv 0) ∧ ν (Rv 1) < 90 ∧ 0 ≤ ν (Rv 0) ∧ -2 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 92 ∧
        -2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 92) := by
  simp [hostGuard, mR, antenna_track_kvretune_IRv2, Run.lowerF, Run.lowerE, hp_1_0, hp_m0_7,
    hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0, hp_90_0,
    hp_0_05, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem sat_guard2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔
      (60 ≤ ν (Rv 0) ∧ 90 ≤ ν (Rv 1) ∧ 0 ≤ ν (Rv 0) ∧ -2 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 92 ∧
        -2 ≤ ν (Rv 2) ∧ ν (Rv 2) ≤ 92) := by
  simp [hostGuard, mR, antenna_track_kvretune_IRv2, Run.lowerF, Run.lowerE, hp_1_0, hp_m0_7,
    hp_30, hp_5_0, hp_0_0, hp_60_0, hp_0_7, hp_46_95, hp_47_05, hp_m2_0, hp_92_0, hp_90_0,
    hp_0_05, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, AOp.interp, Rv, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR antenna_track_kvretune_IRv2 = 1/20 := by
  simp [epsR, antenna_track_kvretune_IRv2, hp_0_05]

/-! ## Existence: the explicit run -/

/-- The command of mode `q` from `c₀`. -/
noncomputable def cSol (q : ℕ) (c0 s : ℝ) : ℝ := c0 + rate q * s

theorem FS_cont (q : ℕ) (x : State (Var 3)) :
    Continuous (fun u => 30 * cSol q (x (Rv 1)) u) := by
  unfold cSol; fun_prop

/-- The run of mode `q` from `x`. -/
noncomputable def phi (q : ℕ) (x : State (Var 3)) (i : Fin 3) (s : ℝ) : ℝ :=
  if i.val = 0 then x (Rv 0) + s
  else if i.val = 1 then cSol q (x (Rv 1)) s
  else forcedSol 30 (x (Rv 2)) (fun u => 30 * cSol q (x (Rv 1)) u) s

theorem phi_0 (q : ℕ) (x : State (Var 3)) : phi q x 0 = fun s => x (Rv 0) + s := by
  funext s; simp [phi]

theorem phi_1 (q : ℕ) (x : State (Var 3)) : phi q x 1 = cSol q (x (Rv 1)) := by
  funext s; simp [phi]

theorem phi_2 (q : ℕ) (x : State (Var 3)) :
    phi q x 2 = forcedSol 30 (x (Rv 2)) (fun u => 30 * cSol q (x (Rv 1)) u) := by
  funext s; simp [phi]

theorem phi_der (q : ℕ) (hq : q < 3) (x : State (Var 3)) (i : Fin 3) (t : ℝ) :
    HasDerivAt (phi q x i) (Term.eval (fR q i) (trajRs x (phi q x) t)) t := by
  match i with
  | 0 =>
      rw [fR0_eval q hq, phi_0]
      exact (hasDerivAt_id' t).const_add (x (Rv 0))
  | 1 =>
      rw [fR1_eval q hq, phi_1]
      unfold cSol
      exact (((hasDerivAt_id' t).const_mul (rate q)).const_add (x (Rv 1))).congr_deriv
        (mul_one _)
  | 2 =>
      rw [fR2_eval q hq, trajRs_R, trajRs_R, phi_1, phi_2]
      exact (forcedSol_hasDerivAt 30 (x (Rv 2)) (FS_cont q x) t).congr_deriv (by ring)

theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 3)) (hd : Formula.sat domR x)
    (hc : ∀ s, 0 ≤ s → s ≤ 1/20 → -2 ≤ cSol q (x (Rv 1)) s ∧ cSol q (x (Rv 1)) s ≤ 92) :
    ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x (1/20) Φ := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := (sat_domR x).mp hd
  refine ⟨_, trajRs_sol x (phi q x) (1/20) (by norm_num) (fun i => ?_)
    (fun i t _ _ => phi_der q hq x i t) (fun t ht hte => ?_)⟩
  · match i with
    | 0 => rw [phi_0]; simp
    | 1 => rw [phi_1]; simp [cSol]
    | 2 => rw [phi_2, forcedSol_zero]
  · have hT := forcedSol_between 30 (x (Rv 2)) (FS_cont q x)
      (lo := -60) (hi := 2760) (T := 1/20) (by norm_num) (fun u hu => by
        have := hc u hu.1 hu.2
        show -60 ≤ 30 * cSol q (x (Rv 1)) u ∧ 30 * cSol q (x (Rv 1)) u ≤ 2760
        constructor <;> linarith [this.1, this.2]) t ⟨ht, hte⟩
    have e1 : (-60 : ℝ) / 30 = -2 := by norm_num
    have e2 : (2760 : ℝ) / 30 = 92 := by norm_num
    rw [e1, e2] at hT
    obtain ⟨c0, c1⟩ := hc t ht hte
    rw [sat_domR]
    simp only [trajRs_R]
    rw [phi_0, phi_1, phi_2]
    exact ⟨by linarith, c0, c1, le_trans (le_min a3 le_rfl) hT.1,
      le_trans hT.2 (max_le a4 le_rfl)⟩

theorem memR (q : ℕ) (i : Fin 3) :
    (Rv i, Term.binop .mul (Term.const 1) (fR q i)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ i

/-- Along every run, the clock and the command are affine. -/
theorem run_affine (q : ℕ) (hq : q < 3) {x : State (Var 3)} {t : ℝ}
    {Φ : ℝ → State (Var 3)} (H : ODESol (modeW q).sys (modeW q).dom x t Φ) :
    Φ t (Rv 0) = x (Rv 0) + t ∧ Φ t (Rv 1) = x (Rv 1) + rate q * t := by
  have h0 : ∀ s, Formula.sat (modeW q).dom s →
      Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = 1 :=
    fun s _ => by rw [eval_unit_mul, fR0_eval q hq]
  have h1 : ∀ s, Formula.sat (modeW q).dom s →
      Term.eval (Term.binop .mul (Term.const 1) (fR q 1)) s = rate q :=
    fun s _ => by rw [eval_unit_mul, fR1_eval q hq]
  have a := H.rate_le (memR q 0) 1 (fun s hs => (h0 s hs).le)
  have b := H.rate_ge (memR q 0) 1 (fun s hs => (h0 s hs).ge)
  have c := H.rate_le (memR q 1) (rate q) (fun s hs => (h1 s hs).le)
  have d := H.rate_ge (memR q 1) (rate q) (fun s hs => (h1 s hs).ge)
  constructor <;> linarith

/-- **Assumption 1 for `antenna_track_kvretune`**, every mode, Z3-free. -/
theorem antenna_track_kvretune_wellFormedR :
    WellFormedR Gr guardR (epsR antenna_track_kvretune_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hc : ∀ s, 0 ≤ s → s ≤ 1/20 →
      -2 ≤ cSol q (x (Rv 1)) s ∧ cSol q (x (Rv 1)) s ≤ 92 := by
    intro s hs0 hs1
    unfold cSol
    interval_cases q
    · -- TRACK: the band keeps `c₀ > 4.95`; `c` falls by at most 0.035
      obtain ⟨g0, g1, -, g3, -, g5, -⟩ := (sat_guard0 x).mp hg
      rw [rate0]; constructor <;> linarith
    · -- STOW: `c₀ < 90` rises by at most 0.25
      obtain ⟨-, g1, -, g3, -⟩ := (sat_guard1 x).mp hg
      rw [rate1]; constructor <;> linarith
    · -- STOWED: `c` frozen
      obtain ⟨-, -, -, g3, g4, -⟩ := (sat_guard2 x).mp hg
      rw [rate2]; constructor <;> linarith
  refine ⟨exists_run q hq3 x hd hc, ?_⟩
  intro t Φ _ H
  have hr := H.hr
  obtain ⟨ht, hcc⟩ := run_affine q hq3 H
  obtain ⟨e0, e1, e2, e3, e4⟩ := (sat_domR _).mp H.end_dom
  interval_cases q
  · -- TRACK: `c + 0.7 t` is kept; TRACK below 60, STOW from 60 (`c ≤ 47.05 < 90`)
    have hg0 := (sat_guard0 x).mp hg
    rw [rate0] at hcc
    by_cases h60 : Φ t (Rv 0) < 60
    · exact ⟨edgeW 0 0, edge_mem 0 0 (by decide),
        (sat_guard0 _).mpr ⟨h60, by linarith [hg0.2.1], by linarith [hg0.2.2.1],
          e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 0 1, edge_mem 0 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith, by linarith [hg0.2.2.1, hg0.2.2.2.1],
          e0, e1, e2, e3, e4⟩⟩
  · -- STOW: `60 ≤ t` is kept; STOW below 90, STOWED from 90
    have hg1 := (sat_guard1 x).mp hg
    by_cases h90 : Φ t (Rv 1) < 90
    · exact ⟨edgeW 1 1, edge_mem 1 1 (by decide),
        (sat_guard1 _).mpr ⟨by linarith [hg1.1], h90, e0, e1, e2, e3, e4⟩⟩
    · exact ⟨edgeW 1 2, edge_mem 1 2 (by decide),
        (sat_guard2 _).mpr ⟨by linarith [hg1.1], by linarith, e0, e1, e2, e3, e4⟩⟩
  · -- STOWED: `t` grows, `c` is frozen at or above 90
    have hg2 := (sat_guard2 x).mp hg
    rw [rate2] at hcc
    exact ⟨edgeW 2 2, edge_mem 2 2 (by decide),
      (sat_guard2 _).mpr ⟨by linarith [hg2.1], by linarith [hg2.2.1], e0, e1, e2, e3, e4⟩⟩

end V2AntennaTrackKvretune
end RelCertifier

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `airheader_dos_3to1`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
three modes and their declared `next` lists, the pruned edges included: Assumption 1 is a fact
of the declared model), the lowered right guards, and `ε_r = 1` read from the file.

The header pressure `p` (coordinate 0) and the frozen demand `g` (coordinate 1, `g' = 0`):
`NORMAL` and `ALARM` run the compressor loop `p' = 0.1 (9 − p) − g p`, `TRIP` the tripped
header `p' = −g p`, all inside `0 ≤ p ≤ 9`, `0.02 ≤ g ≤ 0.06`.
* Existence (i): the explicit exponential at the run's own demand (`exists_run`): with `g`
  frozen at `g₀`, `p' = k (c − p)` with `k = 0.1 + g₀`, `c = 0.9 / k ∈ [0, 9]` (loop), resp.
  `k = g₀`, `c = 0` (trip); `p` stays between `p₀` and `c`, inside the domain.
* (ii), style (b) for `NORMAL` and `ALARM`: a run ends in the domain, and the three guards
  partition `0 ≤ p ≤ 9` (`TRIP` below 5, `ALARM` on `[5, 6)`, `NORMAL` on `[6, 9]`), each a
  declared successor. Style (a) for `TRIP` (latched, `next = [TRIP]`): `p' = −g p ≤ 0` on
  the domain, so `p < 5` is kept and the self-loop is enabled.
Z3-free; modelled on `TankDos3to1.lean` (guards, edges) and `WellFormedR.trajJ_sol` (the
explicit run).
-/
import RelCertifier.InstancesV2.BenchIR.airheader_dos_3to1
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.Proofs.Encoding.GuardedClimb

namespace RelCertifier
namespace V2AirheaderDos3to1

open DL DLCalTiming DLRel Parse Set


def vs : List String := ["p", "g"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := airheader_dos_3to1_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)
noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)
/-! ## Parse pins -/

theorem hp01 : Run.parseRat "0.1" = some ((1:ℚ)/10) := by
  have h : parseQ "0.1" = some (⟨1, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp90 : Run.parseRat "9.0" = some (9 : ℚ) := by
  have h : parseQ "9.0" = some (⟨90, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp50 : Run.parseRat "5.0" = some (5 : ℚ) := by
  have h : parseQ "5.0" = some (⟨50, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp60 : Run.parseRat "6.0" = some (6 : ℚ) := by
  have h : parseQ "6.0" = some (⟨60, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp006 : Run.parseRat "0.06" = some ((3:ℚ)/50) := by
  have h : parseQ "0.06" = some (⟨6, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-! ## The right fields and domain, evaluated -/

/-- `NORMAL`, `ALARM`: the compressor loop `p' = 0.1 (9 − p) − g p`. -/
theorem fLoop_eval (q : ℕ) (hq : q < 2) (x : State (Var 2)) :
    Term.eval (fR q 0) x = 1/10 * (9 - x (Rv 0)) - x (Rv 1) * x (Rv 0) := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, airheader_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp90, hp00,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
      Term.eval, AOp.interp, Rv]

/-- `TRIP`: delivery stopped, `p' = −g p`. -/
theorem fTrip_eval (x : State (Var 2)) :
    Term.eval (fR 2 0) x = -(x (Rv 1) * x (Rv 0)) := by
  simp [fR, hostDyn, mR, airheader_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp00,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost,
    Term.eval, AOp.interp, Rv]

/-- The demand is frozen in every mode. -/
theorem fR1_eval (q : ℕ) (hq : q < 3) (x : State (Var 2)) :
    Term.eval (fR q 1) x = 0 := by
  interval_cases q <;>
    simp [fR, hostDyn, mR, airheader_dos_3to1_IRv2, vs, Run.dynOf, Run.lowerE, hp01, hp90, hp00,
      Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval]

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 9 ∧ 1/50 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 3/50) := by
  simp only [domR, hostEvolve, mR, airheader_dos_3to1_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp90, hp002, hp006, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (NORMAL 0, ALARM 1, TRIP 2). -/
def edgeList : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 2)]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 3) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 3 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 3 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

/-- The demand range every guard carries. -/
def gOK (ν : State (Var 2)) : Prop := 1/50 ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ 3/50

/-- The right guards, evaluated (NORMAL `[6, 9]`, ALARM `[5, 6)`, TRIP `[0, 5)`). -/
theorem sat_guard0 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 0)) ν ↔ (6 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 9) ∧ gOK ν := by
  simp [hostGuard, mR, airheader_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp60, hp90, hp002,
    hp006, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, gOK, and_assoc]

theorem sat_guard1 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 1)) ν ↔ (5 ≤ ν (Rv 0) ∧ ν (Rv 0) < 6) ∧ gOK ν := by
  simp [hostGuard, mR, airheader_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp50, hp60, hp002,
    hp006, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, gOK, and_assoc]

theorem sat_guard2 (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR 2)) ν ↔ (ν (Rv 0) < 5 ∧ 0 ≤ ν (Rv 0)) ∧ gOK ν := by
  simp [hostGuard, mR, airheader_dos_3to1_IRv2, Run.lowerF, Run.lowerE, hp50, hp00, hp002,
    hp006, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv, gOK, and_assoc]

theorem edge_mem (s t : ℕ) (h : (s, t) ∈ edgeList) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), h, rfl⟩, by simp [edgeW]⟩

/-! ## Existence: the explicit exponential at the run's own (frozen) demand -/

/-- A run of every mode, of every duration `ε ≥ 0`, from every domain state: `p` follows
`c + (p₀ − c) e^{−k t}` with `(k, c)` read off the frozen demand, `g` stays. -/
theorem exists_run (q : ℕ) (hq : q < 3) (x : State (Var 2)) (hd : Formula.sat domR x)
    (ε : ℝ) (hε : 0 ≤ ε) : ∃ Φ, ODESol (rightBlock (fR q) (Term.const 1)) domR x ε Φ := by
  obtain ⟨hp0, hp9, hg0, hg1⟩ := (sat_domR x).mp hd
  -- the rate and the target of the frozen-demand contraction
  set k : ℝ := if q = 2 then x (Rv 1) else 1/10 + x (Rv 1) with hkdef
  set c : ℝ := if q = 2 then 0 else (9/10) / (1/10 + x (Rv 1)) with hcdef
  have hk : 0 ≤ k := by rw [hkdef]; split_ifs <;> linarith
  have hc0 : 0 ≤ c := by
    rw [hcdef]; split_ifs
    · exact le_refl 0
    · exact div_nonneg (by norm_num) (by linarith)
  have hc9 : c ≤ 9 := by
    rw [hcdef]; split_ifs
    · norm_num
    · rw [div_le_iff₀ (by linarith)]; linarith
  -- along the trajectory the demand is the start's
  have hfield : ∀ φ : ℝ → ℝ, ∀ t,
      Term.eval (fR q 0) (trajJ x 0 φ t) = k * (c - φ t) := by
    intro φ t
    have hg : trajJ x 0 φ t (Rv 1) = x (Rv 1) := trajJ_Rv_ne x 0 φ t (by decide)
    have hp : trajJ x 0 φ t (Rv 0) = φ t := trajJ_j x 0 φ t
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
    · rw [fLoop_eval 0 (by norm_num), hg, hp, hkdef, hcdef]; simp only [if_neg (by norm_num : (0:ℕ) ≠ 2)]
      field_simp; ring
    · rw [fLoop_eval 1 (by norm_num), hg, hp, hkdef, hcdef]; simp only [if_neg (by norm_num : (1:ℕ) ≠ 2)]
      field_simp; ring
    · rw [fTrip_eval, hg, hp, hkdef, hcdef]; simp only [if_true]; ring
  refine ⟨_, trajJ_sol x 0 (fun t => c + (x (Rv 0) - c) * Real.exp (-(k * t))) ε hε
    (by simp) (fun t _ _ => ?_) (fun i hi t _ _ => ?_) (fun t ht _ => ?_)⟩
  · rw [hfield]
    exact hasDerivAt_expApproach k c (x (Rv 0)) t
  · have hi1 : i = 1 := by
      match i, hi with
      | ⟨1, _⟩, _ => rfl
    subst hi1
    exact fR1_eval q hq _
  · obtain ⟨h1, h2⟩ := exp_approach_between k c (x (Rv 0)) t hk ht
    rw [sat_domR]
    simp only [trajJ_j, trajJ_Rv_ne x 0 _ t (by decide : (1 : Fin 2) ≠ 0)]
    refine ⟨?_, ?_, hg0, hg1⟩
    · exact le_trans (le_min hp0 hc0) h1
    · exact le_trans h2 (max_le hp9 hc9)

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR airheader_dos_3to1_IRv2 = 1 := by
  simp [epsR, airheader_dos_3to1_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

/-- **Assumption 1 for `airheader_dos_3to1`**, every mode, Z3-free. -/
theorem airheader_dos_3to1_wellFormedR :
    WellFormedR Gr guardR (epsR airheader_dos_3to1_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  refine ⟨exists_run q hq3 x hd 1 zero_le_one, ?_⟩
  intro t Φ _ H
  -- the run ends in the domain: `0 ≤ p ≤ 9` and the demand range
  obtain ⟨he0, he9, heg0, heg1⟩ := (sat_domR _).mp H.end_dom
  have hgok : gOK (Φ t) := ⟨heg0, heg1⟩
  have pick : ∀ t', (q, t') ∈ edgeList →
      Formula.sat (hostGuard vs 2 Side.R (mR t')) (Φ t) →
      ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) :=
    fun t' he hs => ⟨edgeW q t', edge_mem q t' he, hs⟩
  -- NORMAL, ALARM: the three guards partition the domain, all three are successors
  have loop : (q, 0) ∈ edgeList → (q, 1) ∈ edgeList → (q, 2) ∈ edgeList →
      ∃ e ∈ Gr.edgesFrom q, Formula.sat (guardR e.tgt) (Φ t) := by
    intro h0 h1 h2
    by_cases h6 : 6 ≤ Φ t (Rv 0)
    · exact pick 0 h0 ((sat_guard0 _).mpr ⟨⟨h6, he9⟩, hgok⟩)
    · by_cases h5 : 5 ≤ Φ t (Rv 0)
      · exact pick 1 h1 ((sat_guard1 _).mpr ⟨⟨h5, lt_of_not_ge h6⟩, hgok⟩)
      · exact pick 2 h2 ((sat_guard2 _).mpr ⟨⟨lt_of_not_ge h5, he0⟩, hgok⟩)
  interval_cases q
  · exact loop (by decide) (by decide) (by decide)
  · exact loop (by decide) (by decide) (by decide)
  · -- TRIP: `p' = −g p ≤ 0` on the domain, so `p < 5` is kept
    obtain ⟨⟨hx5, -⟩, -⟩ := (sat_guard2 x).mp hg
    have hdec := H.rate_le (memR 2) 0 (fun s hs => by
      obtain ⟨hs0, -, hsg, -⟩ := (sat_domR s).mp hs
      rw [eval_unit_mul, fTrip_eval]
      have : 0 ≤ s (Rv 1) * s (Rv 0) := mul_nonneg (by linarith) hs0
      linarith)
    exact pick 2 (by decide) ((sat_guard2 _).mpr ⟨⟨by linarith, he0⟩, hgok⟩)

end V2AirheaderDos3to1
end RelCertifier

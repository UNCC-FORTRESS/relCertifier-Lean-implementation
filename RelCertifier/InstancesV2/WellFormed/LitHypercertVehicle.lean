/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_hypercert_vehicle`: Assumption 1 of the right model (`WellFormedR`)

Model fact, independent of the relational invariant: over the right automaton `Gr` (the file's
five modes and their declared `next` lists), the lowered right guards, and `ε_r = 1` read from
the file.

The right model is the vehicle `(s, v)`: one mode per acceleration `c` (`Am4`, `Am2`, `A0`,
`Ap2`, `Ap4` = `−0.04`, `−0.02`, `0`, `0.02`, `0.04`), `s' = v`, `v' = c`, evolve domain
`s ≥ 0 ∧ 0 ≤ v ≤ 0.6` (every mode); guards `Am4` `v ∈ [0.04, 0.6]`, `Am2` `[0.02, 0.6]`, `A0`
`[0, 0.6]`, `Ap2` `[0, 0.58]`, `Ap4` `[0, 0.56]`; every mode declares all five.
* Existence (i), every mode: the explicit polynomial run `s₀ + v₀ t + c t²/2`, `v₀ + c t`
  (`trajRs_sol`); over `t ∈ [0, 1]` the guard's speed bound keeps `v` in `[0, 0.6]`, and `s`
  stays `≥ 0` because `v` does.
* (ii), every mode (the tool's `exit → Ap4` / `exit → A0` / `invariant` all reduce to this):
  `A0`'s guard is the whole speed range of the domain, so a run's end state, being in the
  domain, is in `A0`'s guard, and the edge into `A0` is declared from every mode.
Z3-free; modelled on `LitDrlCarStop.lean` (the run) and `TankDos3to1.lean` (the layout).
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Proofs.Encoding.WellFormedR
import RelCertifier.InstancesV2.BenchIR.lit_hypercert_vehicle

namespace RelCertifier
namespace V2LitHypercertVehicle

open DL DLCalTiming DLRel Parse Set

def vs : List String := ["s", "v"]
def dm : PMode := ⟨"", [], .tt, .tt, []⟩
def mR (q : ℕ) : PMode := lit_hypercert_vehicle_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 3 → Term (Var 3) := hostDyn vs 3 Side.R (mR q)
noncomputable def domR : Formula (Var 3) := hostEvolve vs 3 Side.R (mR 0)

/-! ## Parse pins -/

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]
theorem hp06 : Run.parseRat "0.6" = some ((3:ℚ)/5) := by
  have h : parseQ "0.6" = some (⟨6, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp004 : Run.parseRat "0.04" = some ((1:ℚ)/25) := by
  have h : parseQ "0.04" = some (⟨4, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp002 : Run.parseRat "0.02" = some ((1:ℚ)/50) := by
  have h : parseQ "0.02" = some (⟨2, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp058 : Run.parseRat "0.58" = some ((29:ℚ)/50) := by
  have h : parseQ "0.58" = some (⟨58, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp056 : Run.parseRat "0.56" = some ((14:ℚ)/25) := by
  have h : parseQ "0.56" = some (⟨56, 100⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num
theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

/-- The accelerations, by mode index. -/
noncomputable def acc : ℕ → ℝ
  | 0 => -1/25 | 1 => -1/50 | 2 => 0 | 3 => 1/50 | _ => 1/25

/-- The guard's speed bounds, by mode index. -/
noncomputable def lo : ℕ → ℝ
  | 0 => 1/25 | 1 => 1/50 | _ => 0

noncomputable def hi : ℕ → ℝ
  | 0 => 3/5 | 1 => 3/5 | 2 => 3/5 | 3 => 29/50 | _ => 14/25

/-- The lowered right fields: `s' = v`, `v' = c_q`, the padding coordinate frozen. -/
theorem fR_eval (q : ℕ) (hq : q < 5) (x : State (Var 3)) (i : Fin 3) :
    Term.eval (fR q i) x =
      if i.val = 0 then x (Rv 1) else if i.val = 1 then acc q else 0 := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mR, lit_hypercert_vehicle_IRv2, vs, Run.dynOf, Run.lowerE, hp00, hp004,
      hp002, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, acc] <;> norm_num

theorem sat_domR (x : State (Var 3)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ 0 ≤ x (Rv 1) ∧ x (Rv 1) ≤ 3/5) := by
  simp only [domR, hostEvolve, mR, lit_hypercert_vehicle_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp06, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv, and_assoc]

/-- The right guards, evaluated (a speed interval per mode, no position bound). -/
theorem sat_guardR (q : ℕ) (hq : q < 5) (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR q)) ν ↔ (lo q ≤ ν (Rv 1) ∧ ν (Rv 1) ≤ hi q) := by
  interval_cases q <;>
    simp [hostGuard, mR, lit_hypercert_vehicle_IRv2, Run.lowerF, Run.lowerE, hp00, hp06, hp004,
      hp002, hp058, hp056, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Rv, lo, hi]

/-! ## The right automaton (the file's modes and declared `next` lists) -/

noncomputable def modeW (q : ℕ) : RMode (Var 3) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

/-- The declared edge `s → t` carries the ENTERED mode's lowered guard. -/
noncomputable def edgeW (s t : ℕ) : REdge (Var 3) :=
  { src := s, tgt := t, guard := hostGuard vs 3 Side.R (mR t), pruned := false }

/-- The declared transitions, as indices (Am4 0, Am2 1, A0 2, Ap2 3, Ap4 4): every mode
declares all five, in the file's order. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
   (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

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

/-- `ε_r` of the file. -/
theorem epsR_eq : epsR lit_hypercert_vehicle_IRv2 = 1 := by
  simp [epsR, lit_hypercert_vehicle_IRv2, hp10]

/-- The lowered right guards. -/
noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

/-! ## Existence: the explicit polynomial run of one period -/

/-- Over one period from a guard state, the run `s₀ + v₀ t + c t²/2`, `v₀ + c t` stays in the domain: the guard's speed bound
keeps `v₀ + c t` in `[0, 0.6]`, and `v₀ t + c t²/2 ≥ 0` because `v₀ + c t ≥ 0`. -/
theorem run_dom (q : ℕ) (hq : q < 5) (x : State (Var 3))
    (hg : lo q ≤ x (Rv 1) ∧ x (Rv 1) ≤ hi q) (hs : 0 ≤ x (Rv 0)) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    0 ≤ x (Rv 0) + x (Rv 1) * t + acc q * t ^ 2 / 2 ∧ 0 ≤ x (Rv 1) + acc q * t ∧
      x (Rv 1) + acc q * t ≤ 3/5 := by
  obtain ⟨hlo, hhi⟩ := hg
  have htt : t ^ 2 ≤ t := by nlinarith
  interval_cases q <;> simp only [lo, hi, acc] at hlo hhi ⊢ <;>
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hlo)]

/-- **Assumption 1 for `lit_hypercert_vehicle`**, every mode, Z3-free. -/
theorem lit_hypercert_vehicle_wellFormedR :
    WellFormedR Gr guardR (epsR lit_hypercert_vehicle_IRv2) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  have hdx := (sat_domR x).mp hd
  refine ⟨?_, ?_⟩
  · -- (i) existence: the explicit polynomial run of one period
    have hd0 : ∀ t : ℝ, HasDerivAt (fun u : ℝ => x (Rv 0) + x (Rv 1) * u + acc q * u ^ 2 / 2)
        (x (Rv 1) + acc q * t) t := fun t => by
      have h1 : HasDerivAt (fun u : ℝ => x (Rv 0) + x (Rv 1) * u) (x (Rv 1)) t := by
        simpa using ((hasDerivAt_id t).const_mul (x (Rv 1))).const_add (x (Rv 0))
      have h2 : HasDerivAt (fun u : ℝ => acc q * u ^ 2 / 2) (acc q * (2 * t ^ 1) / 2) t :=
        ((hasDerivAt_pow 2 t).const_mul (acc q)).div_const 2
      exact (h1.add h2).congr_deriv (by ring)
    refine ⟨_, trajRs_sol (fR := fR q) (domR := domR) x (fun i t =>
        if i.val = 0 then x (Rv 0) + x (Rv 1) * t + acc q * t ^ 2 / 2
        else if i.val = 1 then x (Rv 1) + acc q * t else x (Rv i)) 1 (by norm_num) ?_ ?_ ?_⟩
    · intro i
      fin_cases i <;> simp
    · intro i t _ _
      rw [fR_eval q hq5]
      fin_cases i
      · simpa [trajRs_R] using hd0 t
      · simpa using ((hasDerivAt_id t).const_mul (acc q)).const_add (x (Rv 1))
      · simpa using hasDerivAt_const t (x (Rv 2))
    · intro t ht0 ht1
      rw [sat_domR]
      simpa [trajRs_R] using run_dom q hq5 x hgx hdx.1 t ht0 ht1
  · -- (ii) the end state is in the domain, whose speed range is `A0`'s guard
    intro t Φ _ H
    have hR := (sat_domR _).mp H.end_dom
    refine ⟨edgeW q 2, edge_mem q 2 (by interval_cases q <;> decide), ?_⟩
    exact (sat_guardR 2 (by norm_num) _).mpr (by simp only [lo, hi]; exact hR.2)

end V2LitHypercertVehicle
end RelCertifier


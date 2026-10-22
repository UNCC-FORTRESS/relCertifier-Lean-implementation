/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert`: the right model and Assumption 1 for the nominal model

The right model of the choice exhibit (state variables, right modes, fields, evolve domain,
parse pins, field evaluations, the guarded right automaton `Gr`) and Assumption 1 for the
nominal model (`wellFormedR`, at dimension 2; the bridge instance
`InstancesV2/Bridge/VehicleHypercert.lean` transports it and lifts it by one for the right
clock, and `WellFormedBattery.lean` prints its axioms). Self-contained; the standalone
Theorem 3 leaf `Choice/Modal/VehicleHypercert` imports this file for the right model. The
window data and the hop certificate of the retired standalone route were dropped on
2026-10-22 (history: git show
212cd42:RelCertifier/InstancesV2/Choice/General/VehicleHypercert.lean).
-/
import RelCertifier.InstancesV2.BenchIR.vehicle_hypercert
import RelCertifier.InstancesV2.Choice.ConstMirror
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceVehicleHypercert

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-! ## The right model -/

def vs : List String := ["v"]

def dm : PMode := ⟨"", [], .tt, .tt, []⟩

def mR (q : ℕ) : PMode := vehicle_hypercert_IRv2.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)

noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

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

/-- The accelerations, by mode index. -/
noncomputable def acc : ℕ → ℝ
  | 0 => -1/25 | 1 => -1/50 | 2 => 0 | 3 => 1/50 | _ => 1/25

/-- The guard bounds, by mode index. -/
noncomputable def lo : ℕ → ℝ
  | 0 => 1/25 | 1 => 1/50 | _ => 0

noncomputable def hi : ℕ → ℝ
  | 0 => 3/5 | 1 => 3/5 | 2 => 3/5 | 3 => 29/50 | _ => 14/25

/-- The coordinate field: the acceleration on index 0, the padding index frozen. -/
noncomputable def cf (q : ℕ) : Fin 2 → ℝ := fun i => if i = 0 then acc q else 0

theorem fR_eval (q : ℕ) (hq : q < 5) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fR q i) x = cf q i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mR, vehicle_hypercert_IRv2, vs, Run.dynOf, Run.lowerE, hp00, hp004,
      hp002, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cf, acc] <;> norm_num

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 3/5) := by
  simp only [domR, hostEvolve, mR, vehicle_hypercert_IRv2, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp06, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_guardR (q : ℕ) (hq : q < 5) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ (lo q ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ hi q) := by
  interval_cases q <;>
    simp [hostGuard, mR, vehicle_hypercert_IRv2, Run.lowerF, Run.lowerE, hp00, hp06, hp004,
      hp002, hp058, hp056, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Rv, lo, hi]

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

def edgeList : List (ℕ × ℕ) :=
  (List.range 5).flatMap (fun s => (List.range 5).map (fun t => (s, t)))

theorem edgeList_mem (s t : ℕ) (hs : s < 5) (ht : t < 5) : (s, t) ∈ edgeList := by
  simp [edgeList, hs, ht]

noncomputable def Gr : SearchGraph (Var 2) :=
  { modes := [modeW 0, modeW 1, modeW 2, modeW 3, modeW 4]
    edges := edgeList.map (fun e => edgeW e.1 e.2) }

theorem Gr_modeAt (q : ℕ) (hq : q < 5) : Gr.modeAt q = some (modeW q) := by
  interval_cases q <;> rfl

theorem Gr_modeAt_inv {q : ℕ} {m : RMode (Var 2)} (hm : Gr.modeAt q = some m) :
    q < 5 ∧ m = modeW q := by
  match q with
  | 0 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 1 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 2 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 3 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | 4 => exact ⟨by norm_num, by simpa [SearchGraph.modeAt, Gr] using hm.symm⟩
  | q + 5 => exact absurd hm (by simp [SearchGraph.modeAt, Gr])

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 5 := by decide

theorem edge_mem (s t : ℕ) (hs : s < 5) (ht : t < 5) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), edgeList_mem s t hs ht, rfl⟩, by simp [edgeW]⟩

/-! ## Assumption 1 for the nominal model -/

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR vehicle_hypercert_IRv2 = 1 := by
  simp [epsR, vehicle_hypercert_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem edgesFrom_eq {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    ∃ t, t < 5 ∧ e = edgeW q t := by
  have hmem : e ∈ Gr.edges := List.mem_of_mem_filter he
  have hsrc : e.src = q := by
    unfold SearchGraph.edgesFrom at he
    rw [List.mem_filter] at he
    exact decide_eq_true_eq.mp he.2
  simp only [Gr, List.mem_map] at hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  have hp' := edgeList_tgt p hp
  simp only [edgeW] at hsrc
  subst hsrc
  exact ⟨p.2, hp', rfl⟩

/-- **Assumption 1 for `vehicle_hypercert`**: from every state of a mode's guard the run of one
right interval exists (the guard keeps the velocity in `[0, 0.6]` for one cycle), and every end
state is in the envelope, hence in `A0`'s guard. -/
theorem wellFormedR : WellFormedR Gr guardR 1 := by
  intro q hq m hm x hg hd _
  obtain ⟨hq5, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq5 x).mp hg
  refine ⟨?_, ?_⟩
  · refine odeSol_constRight (fR q) domR x 1 zero_le_one (cf q) (fR_eval q hq5) ?_
    intro t ht0 ht1 y hy
    have hy0 := hy 0
    simp only [cf, if_true] at hy0
    rw [sat_domR, hy0]
    interval_cases q <;> simp only [lo, hi, acc] at hgx ⊢ <;> constructor <;> nlinarith
  · intro t Φ _ H
    have hend : Formula.sat domR (Φ t) := H.hdom t ⟨H.hr, le_rfl⟩
    have hR := (sat_domR _).mp hend
    exact ⟨edgeW q 2, edge_mem q 2 hq5 (by norm_num),
      (sat_guardR 2 (by norm_num) _).mpr (by simp [lo, hi]; exact hR)⟩

/- Theorem-3 part retired 2026-10-21 with the clocked right automaton (the file was fixed at
`Var 2`, no slot for the right clock); the benchmark's Theorem 3 is the generated bridge
instance `InstancesV2/Bridge/VehicleHypercert.lean`.
History: git show 61d7389:RelCertifier/InstancesV2/Choice/General/VehicleHypercert.lean. -/

end ChoiceVehicleHypercert
end RelCertifier

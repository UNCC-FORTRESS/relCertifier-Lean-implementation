/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy`: the right model and Assumption 1 for the nominal model

The right model of the choice exhibit (state variables, right modes, fields, evolve domain,
parse pins, field evaluations, the guarded right automaton `Gr`) and Assumption 1 for the
nominal model (`wellFormedR`, at dimension 2; the bridge instance
`InstancesV2/Bridge/VehicleAccelCopy.lean` transports it and lifts it by one for the right
clock; the bridge instance reads the emitted cut table `Choice/Cuts/vehicle_accel_copy` through this
file, so that leaf is imported here). Self-contained; the standalone Theorem 3 leaf `Choice/Modal/VehicleAccelCopy` imports
this file for the right model. The window data and the hop certificate of the retired
standalone route were dropped on 2026-10-22 (history: git show
212cd42:RelCertifier/InstancesV2/Choice/General/VehicleAccelCopy.lean).
-/
import RelCertifier.InstancesV2.Choice.BenchIR.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.Cuts.vehicle_accel_copy
import RelCertifier.InstancesV2.Choice.ConstMirror
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace ChoiceVehicleAccelCopy

open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-! ## The right model -/

def vs : List String := ["v"]

def dm : PMode := ⟨"", [], .tt, .tt, []⟩

def mR (q : ℕ) : PMode := vehicle_accel_copy_IRc.R.modes.getD q dm

noncomputable def fR (q : ℕ) : Fin 2 → Term (Var 2) := hostDyn vs 2 Side.R (mR q)

noncomputable def domR : Formula (Var 2) := hostEvolve vs 2 Side.R (mR 0)

theorem hp00 : Run.parseRat "0.0" = some (0 : ℚ) := by
  have h : parseQ "0.0" = some (⟨0, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem hp300 : Run.parseRat "30.0" = some (30 : ℚ) := by
  have h : parseQ "30.0" = some (⟨300, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp270 : Run.parseRat "27.0" = some (27 : ℚ) := by
  have h : parseQ "27.0" = some (⟨270, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

theorem hp30 : Run.parseRat "3.0" = some (3 : ℚ) := by
  have h : parseQ "3.0" = some (⟨30, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]; norm_num

/-- The accelerations, by mode index. -/
noncomputable def acc : ℕ → ℝ
  | 0 => 1 | 1 => 0 | _ => -1

noncomputable def loR : ℕ → ℝ
  | 0 => 0 | 1 => 0 | _ => 3

noncomputable def hiR : ℕ → ℝ
  | 0 => 27 | _ => 30

/-- The coordinate field: the acceleration on index 0, the padding index frozen. -/
noncomputable def cf (q : ℕ) : Fin 2 → ℝ := fun i => if i = 0 then acc q else 0

theorem fR_eval (q : ℕ) (hq : q < 3) (i : Fin 2) (x : State (Var 2)) :
    Term.eval (fR q i) x = cf q i := by
  fin_cases i <;> interval_cases q <;>
    simp [fR, hostDyn, mR, vehicle_accel_copy_IRc, vs, Run.dynOf, Run.lowerE, hp00, hp10, Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
      AOp.interp, Rv, cf, acc] <;> norm_num

theorem sat_domR (x : State (Var 2)) :
    Formula.sat domR x ↔ (0 ≤ x (Rv 0) ∧ x (Rv 0) ≤ 30) := by
  simp only [domR, hostEvolve, mR, vehicle_accel_copy_IRc, vs]
  simp [Run.lowerF, Run.lowerE, hp00, hp300, Run.resolveVar, List.findIdx?_cons,
    IForm.toHost, ITerm.toHost, Formula.sat, CompOp.interp, Term.eval, Rv]

theorem sat_guardR (q : ℕ) (hq : q < 3) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔ (loR q ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ hiR q) := by
  interval_cases q <;>
    simp [hostGuard, mR, vehicle_accel_copy_IRc, Run.lowerF, Run.lowerE, hp00, hp270, hp300,
      hp30, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost,
      Formula.sat, CompOp.interp, Term.eval, Rv, loR, hiR]

noncomputable def modeW (q : ℕ) : RMode (Var 2) :=
  { sys := rightBlock (fR q) (Term.const 1), dom := domR, weight := 1 }

noncomputable def edgeW (s t : ℕ) : REdge (Var 2) :=
  { src := s, tgt := t, guard := hostGuard vs 2 Side.R (mR t), pruned := false }

def edgeList : List (ℕ × ℕ) :=
  (List.range 3).flatMap (fun s => (List.range 3).map (fun t => (s, t)))

theorem edgeList_mem (s t : ℕ) (hs : s < 3) (ht : t < 3) : (s, t) ∈ edgeList := by
  simp [edgeList, hs, ht]

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

theorem edgeList_tgt : ∀ p ∈ edgeList, p.2 < 3 := by decide

theorem edge_mem (s t : ℕ) (hs : s < 3) (ht : t < 3) : edgeW s t ∈ Gr.edgesFrom s :=
  List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(s, t), edgeList_mem s t hs ht, rfl⟩, by simp [edgeW]⟩

/-! ## Assumption 1 for the nominal model -/

theorem epsR_eq : epsR vehicle_accel_copy_IRc = 1 := by
  simp [epsR, vehicle_accel_copy_IRc, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem edgesFrom_eq {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    ∃ t, t < 3 ∧ e = edgeW q t := by
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

/-- **Assumption 1 for `vehicle_accel_copy`**: from every state of a mode's guard the run of
one right interval exists (the guard keeps the velocity in `[0, 30]` for one cycle), and every
end state is in the envelope, hence in `Coast`'s guard. -/
theorem wellFormedR : WellFormedR Gr guardR 1 := by
  intro q hq m hm x hg hd _
  obtain ⟨hq3, rfl⟩ := Gr_modeAt_inv hm
  have hgx := (sat_guardR q hq3 x).mp hg
  refine ⟨?_, ?_⟩
  · refine odeSol_constRight (fR q) domR x 1 zero_le_one (cf q) (fR_eval q hq3) ?_
    intro t ht0 ht1 y hy
    have hy0 := hy 0
    simp only [cf, if_true] at hy0
    rw [sat_domR, hy0]
    interval_cases q <;> simp only [loR, hiR, acc] at hgx ⊢ <;> constructor <;> nlinarith
  · intro t Φ _ H
    have hend : Formula.sat domR (Φ t) := H.hdom t ⟨H.hr, le_rfl⟩
    have hR := (sat_domR _).mp hend
    exact ⟨edgeW q 1, edge_mem q 1 hq3 (by norm_num),
      (sat_guardR 1 (by norm_num) _).mpr (by simp [loR, hiR]; exact hR)⟩

/- Theorem-3 part retired 2026-10-21 with the clocked right automaton (the file was fixed at
`Var 2`, no slot for the right clock); the benchmark's Theorem 3 is the generated bridge
instance `InstancesV2/Bridge/VehicleAccelCopy.lean`.
History: git show 61d7389:RelCertifier/InstancesV2/Choice/General/VehicleAccelCopy.lean. -/

end ChoiceVehicleAccelCopy
end RelCertifier

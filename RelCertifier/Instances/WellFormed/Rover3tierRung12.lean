/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12`: Assumption 1 of the right model (`WellFormedR`)

Over the guarded right automaton `GrG` of the Theorem 3 instance
(`Instances/Rover3tierRung12Guarded.lean`), the lowered right guards, `ε_r = 0.3` (the
literal is the suite_v2 file's, `InstancesV2/SameIR.lean`). Both modes run `v' = a`,
`s' = v`, `a' = 0` with `a ∈ [0.5, 1]` on the evolve domain, so `v` only grows.
* `ACCEL` (`0.3 ≤ v < 0.6`), style (b): a run ends at `v ≥ v₀ ≥ 0.3`, inside `ACCEL` or
  `COAST` (`v ≥ 0.6`).
* `COAST` (`v ≥ 0.6`), style (a): forward invariant.
Existence: the instance's explicit polynomial run (`runEnd`). Z3-free.
-/
import RelCertifier.Instances.Rover3tierRung12Guarded
import RelCertifier.Proofs.Encoding.WellFormedR

namespace RelCertifier
namespace Rover3tierRung12Guarded

open DL DLCalTiming DLRel Parse Set Rover3tierRung12Modal Rover3tierRung12Handoff

theorem epsR_eq : epsR rover3tier_rung12_IR = 3/10 := by
  simp [epsR, rover3tier_rung12_IR, hq03]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vsQ 3 Side.R (mRQ q)

/-- **Assumption 1 for `rover3tier_rung12`**, every mode, Z3-free. -/
theorem rover3tier_rung12_wellFormedR :
    WellFormedR GrG guardR (epsR rover3tier_rung12_IR) := by
  rw [epsR_eq]
  intro q hq m hm x hg hd _
  rw [GrG_len] at hq
  have hmq : m = modeQ q := by
    have := GrG_modeAt q hq; rw [hm] at this; exact Option.some.inj this
  subst hmq
  refine ⟨⟨_, run_sol q hq x hd (3/10) (by norm_num)⟩, ?_⟩
  intro t Φ _ H
  have hmono := H.mono (rightBlock_mem' (fRQ q) (Term.const 1) 0) (fun s hs => by
    rw [eval_unit_mul, fRQ0_eval q hq]
    have := ((sat_domRQ s).mp hs).1; linarith)
  have hgx := (sat_guardRQ q hq x).mp hg
  interval_cases q
  · simp only [if_true] at hgx
    by_cases h06 : Φ t (Rv 0) < 3/5
    · exact ⟨edgeG 0 0, edgeG_mem 0 0 (by norm_num) (by norm_num),
        (sat_guardRQ 0 (by norm_num) _).mpr (by simp only [if_true]; exact ⟨by linarith, h06⟩)⟩
    · exact ⟨edgeG 0 1, edgeG_mem 0 1 (by norm_num) (by norm_num),
        (sat_guardRQ 1 (by norm_num) _).mpr (by norm_num; linarith)⟩
  · norm_num at hgx
    exact ⟨edgeG 1 1, edgeG_mem 1 1 (by norm_num) (by norm_num),
      (sat_guardRQ 1 (by norm_num) _).mpr (by norm_num; linarith)⟩

end Rover3tierRung12Guarded
end RelCertifier

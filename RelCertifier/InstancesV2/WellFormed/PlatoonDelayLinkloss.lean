/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_linkloss`: Assumption 1 of the right model — FALSE (model defect)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false** (`platoon_delay_linkloss_wellFormedR_false`): the AEB sink `BRAKE`
(guard `g < 20`, flow `g' = 1.5`, declared successors `[BRAKE]` only) is left by its own
flow. From `g = 19` (inside the guard and the evolve domain `0 ≤ g ≤ 60`) the run of
duration `ε_r = 1` ends at `g = 20.5`, where no declared successor of `BRAKE` is enabled:
the nominal controller blocks. (`BRAKE` is a pruned sink: the certificate never enters it
from the region of the Theorem 3 statement, which therefore does not depend on it.)

**Every other mode satisfies Assumption 1** (`platoon_delay_linkloss_wellFormedR_modes`,
style (a), Z3-free): `FOLLOW` (`20 ≤ g < 40`, `g' = −0.5 (g − 30)`) and `CATCH` (`g ≥ 30`,
`g' = −0.6 (g − 30)`) are contractions toward 30 whose guard sets are forward invariant.
-/
import RelCertifier.InstancesV2.Modal.PlatoonDelayLinkloss
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2PlatoonDelayLinkloss

open DL DLCalTiming DLRel Parse Set

theorem epsR_eq : epsR platoon_delay_linkloss_IRv2 = 1 := by
  simp [epsR, platoon_delay_linkloss_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 3) := hostGuard vs 3 Side.R (mR q)

theorem fR0_brake (x : State (Var 3)) : Term.eval (fR 2 0) x = 3/2 := by
  simp [fR, hostDyn, mR, platoon_delay_linkloss_IRv2, vs, Run.dynOf, Run.lowerE, hp15,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_guardR2 (ν : State (Var 3)) :
    Formula.sat (hostGuard vs 3 Side.R (mR 2)) ν ↔ ν (Rv 0) < 20 := by
  simp [hostGuard, mR, platoon_delay_linkloss_IRv2, Run.lowerF, Run.lowerE, hp200, vs,
    Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
    CompOp.interp, Term.eval, Rv]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 3)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `FOLLOW` and `CATCH`** (style (a), Z3-free). -/
theorem platoon_delay_linkloss_wellFormedR_modes (q : ℕ) (hq : q < 2) :
    WellFormedRMode Gr guardR (epsR platoon_delay_linkloss_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hgx := (sat_guardR q hq x).mp hg
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) 30 hk (fR0_eval q hq)
      (fun i hi s => fR_pad q (by omega) i hi s) ?_ 1 (by norm_num)
    intro v h1 h2
    show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    exact ⟨le_trans (le_min hdx.1 (by norm_num)) h1, le_trans h2 (max_le hdx.2 (by norm_num))⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (30 - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq]
    have hb := H.linear_between (memR q) _ _ hk hf
    interval_cases q
    · -- FOLLOW: [20, 40) invariant
      simp only [if_true] at hgx
      exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR 0 (by norm_num) _).mpr
        (by simp only [if_true]; exact ⟨le_trans (le_min hgx.1 (by norm_num)) hb.1,
          lt_of_le_of_lt hb.2 (max_lt hgx.2 (by norm_num))⟩)⟩
    · -- CATCH: g ≥ 30 invariant
      norm_num at hgx
      exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR 1 (by norm_num) _).mpr
        (by norm_num; exact le_trans (le_min hgx le_rfl) hb.1)⟩

/-- The witness state: `g = 19` (every other variable 0). -/
noncomputable def x19 : State (Var 3) := fun y => if y = Rv 0 then 19 else 0

/-- **Assumption 1 fails at `BRAKE`**: from `g = 19` the run of duration 1 ends at
`g = 20.5`, outside `BRAKE`'s guard, and `BRAKE`'s only declared successor is itself. -/
theorem platoon_delay_linkloss_brake_blocks :
    ¬ WellFormedRMode Gr guardR (epsR platoon_delay_linkloss_IRv2) 2 := by
  rw [epsR_eq]
  have H := exists_rate_run (fR := fR 2) (domR := domR) x19 0 (3/2) fR0_brake
    (fun i hi s => fR_pad 2 (by norm_num) i hi s) 1 (by norm_num)
    (fun t ht ht1 => by
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      simp only [x19, if_true]
      constructor <;> linarith)
  refine not_wellFormedR_of_run (Gr_modeAt 2 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 3 Side.R (mR 2)) x19
    rw [sat_guardR2]; simp [x19]; norm_num
  · show Formula.sat domR x19
    rw [sat_domR]; simp [x19]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    have ht : e.tgt = 2 := by simp [edgeList] at hl; exact hl
    rw [ht] at hsat
    have := (sat_guardR2 _).mp hsat
    simp [x19] at this
    linarith

/-- **`platoon_delay_linkloss` violates Assumption 1** (a model defect: the AEB sink `BRAKE`
blocks; see the module docstring). -/
theorem platoon_delay_linkloss_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR platoon_delay_linkloss_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) platoon_delay_linkloss_brake_blocks

end V2PlatoonDelayLinkloss
end RelCertifier

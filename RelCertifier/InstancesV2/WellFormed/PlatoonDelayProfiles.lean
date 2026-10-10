/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_profiles`: Assumption 1 of the right model — FALSE (model defect)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` is false** (`platoon_delay_profiles_wellFormedR_false`): the AEB sink `BRAKE`
(guard `g < 20`, flow `g' = 1.5`, declared successors `[BRAKE]` only) is left by its own
flow: from `g = 19` the run of duration 1 ends at `g = 20.5`, where no declared successor of
`BRAKE` is enabled. (`BRAKE` is a pruned sink, never entered by the Theorem 3 responses.)

**Every other mode satisfies Assumption 1** (`platoon_delay_profiles_wellFormedR_modes`,
style (a), Z3-free): `FOLLOW` (`20 ≤ g ≤ 40`), `GENTLE`, `ASSERTIVE` (`g ≥ 30`) are
contractions toward 30 whose guard sets are forward invariant.
-/
import RelCertifier.InstancesV2.Modal.PlatoonDelayProfiles
import RelCertifier.Proofs.Encoding.WellFormedR

set_option linter.unusedSimpArgs false

namespace RelCertifier
namespace V2PlatoonDelayProfiles

open DL DLCalTiming DLRel Parse Set

theorem hp10 : Run.parseRat "1.0" = some (1 : ℚ) := by
  have h : parseQ "1.0" = some (⟨10, 10⟩ : QF) := by decide
  simp [Run.parseRat, h]

theorem epsR_eq : epsR platoon_delay_profiles_IRv2 = 1 := by
  simp [epsR, platoon_delay_profiles_IRv2, hp10]

noncomputable def guardR (q : ℕ) : Formula (Var 2) := hostGuard vs 2 Side.R (mR q)

theorem fR0_brake (x : State (Var 2)) : Term.eval (fR 3 0) x = 3/2 := by
  simp [fR, hostDyn, mR, platoon_delay_profiles_IRv2, vs, Run.dynOf, Run.lowerE, hp15,
    Run.resolveVar, List.findIdx?_cons, List.finRange, ITerm.toHost, Term.eval,
    AOp.interp, Rv]

theorem sat_guardR' (q : ℕ) (hq : q < 4) (ν : State (Var 2)) :
    Formula.sat (hostGuard vs 2 Side.R (mR q)) ν ↔
      (if q = 0 then 20 ≤ ν (Rv 0) ∧ ν (Rv 0) ≤ 40
       else if q = 3 then ν (Rv 0) < 20 else 30 ≤ ν (Rv 0)) := by
  interval_cases q <;>
    simp [hostGuard, mR, platoon_delay_profiles_IRv2, Run.lowerF, Run.lowerE, hp200, hp400,
      hp300, vs, Run.resolveVar, List.findIdx?_cons, IForm.toHost, ITerm.toHost, Formula.sat,
      CompOp.interp, Term.eval, Rv]

theorem memR (q : ℕ) : (Rv 0, Term.binop .mul (Term.const 1) (fR q 0)) ∈ (modeW q).sys :=
  rightBlock_mem' _ _ 0

theorem edgesFrom_list {q : ℕ} {e : REdge (Var 2)} (he : e ∈ Gr.edgesFrom q) :
    (q, e.tgt) ∈ edgeList :=
  edgesFrom_mem_list (L := edgeList) (f := fun p => edgeW p.1 p.2) rfl
    (fun _ => ⟨rfl, rfl⟩) he

/-- **Assumption 1 at `FOLLOW`, `GENTLE`, `ASSERTIVE`** (style (a), Z3-free). -/
theorem platoon_delay_profiles_wellFormedR_modes (q : ℕ) (hq : q < 3) :
    WellFormedRMode Gr guardR (epsR platoon_delay_profiles_IRv2) q := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hgx := (sat_guardR' q (by omega) x).mp hg
  have hk : 0 ≤ kR q := by unfold kR; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · refine exists_contract_run x 0 (kR q) (cRc q) hk (fR0_eval q hq)
      ?_ ?_ 1 (by norm_num)
    · intro i hi s
      match i, hi with
      | 1, _ => exact fR1_eval q (by omega) s
    · intro v h1 h2
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      exact ⟨le_trans (le_min hdx.1 (by simp [cRc])) h1,
        le_trans h2 (max_le hdx.2 (by simp [cRc]; norm_num))⟩
  · intro t Φ _ H
    have hf : ∀ s, Formula.sat (modeW q).dom s →
        Term.eval (Term.binop .mul (Term.const 1) (fR q 0)) s = kR q * (cRc q - s (Rv 0)) :=
      fun s _ => by rw [eval_unit_mul, fR0_eval q hq]
    have hb := H.linear_between (memR q) _ _ hk hf
    simp only [cRc] at hb
    interval_cases q
    · simp only [if_true] at hgx
      exact ⟨edgeW 0 0, edge_mem 0 0 (by decide), (sat_guardR' 0 (by norm_num) _).mpr
        (by simp only [if_true]; exact ⟨le_trans (le_min hgx.1 (by norm_num)) hb.1,
          le_trans hb.2 (max_le hgx.2 (by norm_num))⟩)⟩
    · norm_num at hgx
      exact ⟨edgeW 1 1, edge_mem 1 1 (by decide), (sat_guardR' 1 (by norm_num) _).mpr
        (by norm_num; exact le_trans (le_min hgx le_rfl) hb.1)⟩
    · norm_num at hgx
      exact ⟨edgeW 2 2, edge_mem 2 2 (by decide), (sat_guardR' 2 (by norm_num) _).mpr
        (by norm_num; exact le_trans (le_min hgx le_rfl) hb.1)⟩

/-- The witness state: `g = 19` (every other variable 0). -/
noncomputable def x19 : State (Var 2) := fun y => if y = Rv 0 then 19 else 0

/-- **Assumption 1 fails at `BRAKE`**: from `g = 19` the run of duration 1 ends at
`g = 20.5`, outside `BRAKE`'s guard; `BRAKE`'s only declared successor is itself. -/
theorem platoon_delay_profiles_brake_blocks :
    ¬ WellFormedRMode Gr guardR (epsR platoon_delay_profiles_IRv2) 3 := by
  rw [epsR_eq]
  have H := exists_rate_run (fR := fR 3) (domR := domR) x19 0 (3/2) fR0_brake
    (fun i hi s => by
      match i, hi with
      | 1, _ => exact fR1_eval 3 (by norm_num) s) 1 (by norm_num)
    (fun t ht ht1 => by
      show Formula.sat domR _
      rw [sat_domR, trajJ_j]
      simp only [x19, if_true]
      constructor <;> linarith)
  refine not_wellFormedR_of_run (Gr_modeAt 3 (by norm_num)) ?_ ?_ le_rfl H ?_
  · show Formula.sat (hostGuard vs 2 Side.R (mR 3)) x19
    rw [sat_guardR' 3 (by norm_num)]; simp [x19]; norm_num
  · show Formula.sat domR x19
    rw [sat_domR]; simp [x19]; norm_num
  · intro e he hsat
    have hl := edgesFrom_list he
    have ht : e.tgt = 3 := by simp [edgeList] at hl; exact hl
    rw [ht] at hsat
    have := (sat_guardR' 3 (by norm_num) _).mp hsat
    simp [x19] at this
    linarith

/-- **`platoon_delay_profiles` violates Assumption 1** (a model defect: the AEB sink `BRAKE`
blocks). -/
theorem platoon_delay_profiles_wellFormedR_false :
    ¬ WellFormedR Gr guardR (epsR platoon_delay_profiles_IRv2) :=
  not_wellFormedR_of_mode (by simp [Gr]) platoon_delay_profiles_brake_blocks

end V2PlatoonDelayProfiles
end RelCertifier

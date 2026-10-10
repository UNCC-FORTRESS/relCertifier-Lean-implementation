/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_profiles`: Assumption 1 of the right model — PROVED (repaired model)

Over the instance's guarded right automaton `Gr`, the lowered right guards, `ε_r = 1`.

**`WellFormedR` holds** (`platoon_delay_profiles_wellFormedR`, Z3-free):

* `FOLLOW` (`20 ≤ g ≤ 40`), `GENTLE`, `ASSERTIVE` (`g ≥ 30`): contractions toward 30 whose
  guard sets are forward invariant (style (a));
* `BRAKE` (`g < 20`, `g' = 1.5`, declared successors `[BRAKE, FOLLOW]`: the brake re-engages
  `FOLLOW` once the gap is back at 20 m, the 2026-10-10 repair, `docs/SUITE-REDESIGN.md`
  §21): style (b). A run of duration `t ≤ 1` from `g < 20` ends below `21.5`: in `BRAKE`'s
  guard if below 20, else in `FOLLOW`'s.

(Until 2026-10-10 `BRAKE`'s only successor was itself and the model was refuted here, from
`g = 19`: the run of duration 1 ends at `g = 20.5`.)
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

/-- **Assumption 1 at `BRAKE`** (style (b)): the gap reopens at `1.5 m/s`; every run of at
most one interval ends below `21.5`, in `BRAKE`'s guard or in `FOLLOW`'s. -/
theorem platoon_delay_profiles_wellFormedR_brake :
    WellFormedRMode Gr guardR (epsR platoon_delay_profiles_IRv2) 3 := by
  rw [epsR_eq]
  refine wellFormedRMode_intro (fun m hm x hg hd => ?_)
  obtain ⟨-, rfl⟩ := Gr_modeAt_inv hm
  have hdx := (sat_domR x).mp hd
  have hgx : x (Rv 0) < 20 := by
    have := (sat_guardR' 3 (by norm_num) x).mp hg; simpa using this
  refine ⟨⟨_, exists_rate_run (fR := fR 3) (domR := domR) x 0 (3/2) fR0_brake
    (fun i hi s => by
      match i, hi with
      | 1, _ => exact fR1_eval 3 (by norm_num) s) 1 (by norm_num) (fun t ht ht1 => ?_)⟩, ?_⟩
  · show Formula.sat domR _
    rw [sat_domR, trajJ_j]
    constructor <;> nlinarith [hdx.1, hdx.2]
  · intro t Φ ht H
    have hup := H.rate_le (memR 3) (3/2) (fun s _ => by rw [eval_unit_mul, fR0_brake])
    have hlo := H.mono (memR 3) (fun s _ => by rw [eval_unit_mul, fR0_brake]; norm_num)
    have ht0 := H.hr
    by_cases h20 : Φ t (Rv 0) < 20
    · exact ⟨edgeW 3 3, edge_mem 3 3 (by decide), (sat_guardR' 3 (by norm_num) _).mpr
        (by simpa using h20)⟩
    · push_neg at h20
      refine ⟨edgeW 3 0, edge_mem 3 0 (by decide), (sat_guardR' 0 (by norm_num) _).mpr ?_⟩
      rw [if_pos rfl]
      exact ⟨h20, by nlinarith⟩

/-- **`platoon_delay_profiles` satisfies Assumption 1** (every mode, Z3-free). -/
theorem platoon_delay_profiles_wellFormedR :
    WellFormedR Gr guardR (epsR platoon_delay_profiles_IRv2) := by
  intro q hq
  have hq4 : q < 4 := by simpa [Gr] using hq
  rcases (by omega : q < 3 ∨ q = 3) with h | rfl
  · exact platoon_delay_profiles_wellFormedR_modes q h
  · exact platoon_delay_profiles_wellFormedR_brake

end V2PlatoonDelayProfiles
end RelCertifier

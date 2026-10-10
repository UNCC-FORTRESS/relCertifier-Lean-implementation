/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The carried-over non-connection certificate, pinned to the suite_v2 runner

`Instances/MatchMultiRatePruned.match_multi_rate_nonconn` (re-exported by
`InstancesV2/BatteryV2`) states Theorem 2 for the pruned right edge `DRIVE → STALL` of
`match_multi_rate`, under the hypothesis `VerdNC`: the two pruning queries the certifier
sent Z3 (`Trusted/NonConnQuery.lean`: the source check and the barrier check) come back
`unsat`. This file proves that the pair the suite_v2 non-connection phase
(`VerdictsV2.runNonConnAllV2`, part of `relcert --run-verdicts-v2`) rebuilds for that edge,
from the suite_v2 IR and the extended cut certificate, IS the pair `VerdNC` names, and that
the edge is in the phase's work list. So the phase's two `UNSAT` lines for
`match_multi_rate DRIVE -> STALL` discharge `VerdNC`.

The extended certificate's `DRIVE` atoms are the two guard conjuncts `v ≥ 0.2`, `v ≤ 1`,
the same atoms as the legacy certificate the instance quotes, and the suite_v2 literal is
the legacy literal (`InstancesV2/SameIR.lean`); both facts are checked here by `decide`.
-/
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.Instances.MatchMultiRatePruned

set_option autoImplicit false

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.NonConn RelCertifier.MatchMultiRatePruned
  RelCertifier.MatchMultiRateModal

/-- The runner's IR for `match_multi_rate` is the literal the instance quotes. -/
theorem irV2_match_multi_rate : irV2 "match_multi_rate" = match_multi_rate_IR := by decide

/-- The source mode's cut atoms the runner folds are the instance's. -/
theorem cutAtoms_match_multi_rate_DRIVE :
    (cutAtomsOfX (cutV2 "match_multi_rate").R "DRIVE").map (·.atom)
      = rightCutAtoms Oracle.match_multi_rate_cuts "DRIVE" := by decide

/-- The runner lowers over the instance's variable list. -/
theorem jointVars_match_multi_rate : match_multi_rate_IR.jointVars = vsM := by decide

/-- The suite_v2 runner's rebuilt pair for `DRIVE → STALL` is the instance's
`(srcQuery …, barQuery …)`. -/
theorem nonconn_pin_MatchMultiRateV2 :
    nonConnQueriesOfV2 (irV2 "match_multi_rate") (cutV2 "match_multi_rate") "DRIVE" "STALL"
      = some ⟨2, fun i => vsM.getD i.val s!"pad{i.val}",
          srcQuery gD srcD cutD, barQuery gD domD cutD fD⟩ := by
  unfold nonConnQueriesOfV2
  rw [irV2_match_multi_rate, cutAtoms_match_multi_rate_DRIVE, jointVars_match_multi_rate]
  have h0 : match_multi_rate_IR.R.modes.find? (·.name == "DRIVE") = some (mRM 0) := by decide
  have h1 : match_multi_rate_IR.R.modes.find? (·.name == "STALL") = some (mRM 1) := by decide
  simp only [h0, h1, Option.bind_eq_bind, Option.bind_some]
  change (cutOfAtoms vsM 2 (rightCutAtoms Oracle.match_multi_rate_cuts "DRIVE")).bind
      (fun cutR : IForm 2 => (queries vsM 2 cutR (mRM 0) (mRM 1)).bind
        (fun d : IForm 2 × IForm 2 =>
          (pure (⟨2, (fun i => vsM.getD i.val s!"pad{i.val}", d.1, d.2)⟩ :
            (n : ℕ) × (Fin n → String) × IForm n × IForm n) :
            Option ((n : ℕ) × (Fin n → String) × IForm n × IForm n)))) = _
  rw [hcutD, Option.bind_some, queriesD]
  rfl

/-- The edge is in the phase's work list (the pruned edges of the emitted suite_v2 covers). -/
theorem prunedEdgesV2_match_multi_rate :
    ("match_multi_rate", "DRIVE", "STALL") ∈ prunedEdgesV2 := by decide

/-- `VerdNC` is exactly the two facts the phase discharges for that edge. -/
theorem VerdNC_iff :
    VerdNC ↔ (z3solve (srcQuery gD srcD cutD).toHost = Verdict.unsat ∧
      z3solve (barQuery gD domD cutD fD).toHost = Verdict.unsat) := Iff.rfl

end RelCertifier.VerdictsV2

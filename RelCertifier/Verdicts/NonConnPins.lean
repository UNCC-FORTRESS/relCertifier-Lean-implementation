/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Non-connection pins — the runner's rebuilt pruning queries ARE the instance's hypothesis

`Verdicts/RunNonConn.lean` rebuilds, for every pruned edge the emitted covers record, the
two queries the certifier sent Z3 (`nonConnQueriesOf`, over the emitted IR and cut
certificate, through `Trusted/NonConnQuery.lean`). `Instances/MatchMultiRatePruned.lean`
states the certificate's two verdicts as `VerdNC` over explicit IR literals. This file
proves, by `rfl` after the instance's own lowering pins, that the pair the runner prints
for `DRIVE → STALL` is exactly the pair `VerdNC` names — so a green `UNSAT [source]` /
`UNSAT [barrier]` line is evidence about the theorem's hypothesis and not about a
lookalike (the same discipline as `ModalPinTable` for the modal packs).

Three facts per pruned edge:

* the runner's variable list is the instance's (`jointVars` is `vsM`: both sides declare
  the same variables);
* the runner's rebuilt pair is the instance's `(srcQuery …, barQuery …)`;
* `VerdNC` is the conjunction of `z3solve (q).toHost = unsat` over that pair, i.e.
  what phase 5 discharges.
-/
import RelCertifier.Verdicts.RunNonConn
import RelCertifier.Instances.MatchMultiRatePruned

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.NonConn RelCertifier.MatchMultiRatePruned
  RelCertifier.MatchMultiRateModal

set_option autoImplicit false

/-- The runner lowers `match_multi_rate` over the instance's variable list. -/
theorem jointVars_MatchMultiRate : match_multi_rate_IR.jointVars = vsM := by decide

/-- The runner's rebuilt pair for the pruned edge `DRIVE → STALL` is the instance's. -/
theorem nonconn_pin_MatchMultiRate :
    nonConnQueriesOf match_multi_rate_IR Oracle.match_multi_rate_cuts "DRIVE" "STALL"
      = some ⟨2, fun i => vsM.getD i.val s!"pad{i.val}",
          srcQuery gD srcD cutD, barQuery gD domD cutD fD⟩ := by
  unfold nonConnQueriesOf
  rw [jointVars_MatchMultiRate]
  have h0 : match_multi_rate_IR.R.modes.find? (·.name == "DRIVE") = some (mRM 0) := by decide
  have h1 : match_multi_rate_IR.R.modes.find? (·.name == "STALL") = some (mRM 1) := by decide
  simp only [h0, h1, Option.bind_eq_bind, Option.bind_some]
  -- `vsM.length` is `2` by unfolding; restate the goal at `2` so the pins rewrite
  change (cutOfAtoms vsM 2 (rightCutAtoms Oracle.match_multi_rate_cuts "DRIVE")).bind
      (fun cutR : IForm 2 => (queries vsM 2 cutR (mRM 0) (mRM 1)).bind
        (fun d : IForm 2 × IForm 2 =>
          (pure (⟨2, (fun i => vsM.getD i.val s!"pad{i.val}", d.1, d.2)⟩ :
            (n : ℕ) × (Fin n → String) × IForm n × IForm n) :
            Option ((n : ℕ) × (Fin n → String) × IForm n × IForm n)))) = _
  rw [hcutD, Option.bind_some, queriesD]
  rfl

/-- The pruned edge the runner walks is the one the instance certifies, and it is the
only one in the suite. -/
theorem prunedEdges_MatchMultiRate :
    prunedEdges = [("match_multi_rate", "DRIVE", "STALL")] := by decide

/-- `VerdNC` is exactly the two facts phase 5 discharges. -/
theorem VerdNC_iff :
    VerdNC ↔ (z3solve (srcQuery gD srcD cutD).toHost = Verdict.unsat ∧
      z3solve (barQuery gD domD cutD fD).toHost = Verdict.unsat) := Iff.rfl

end RelCertifier.Verdicts

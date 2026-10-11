/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 declared coverage, derived from the tables (cannot drift)

Each declared count in `RunV2` is proved equal to what the table that generates the work
produces, so the constants and the suite (or the pack table) can only change together.
-/
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.Verdicts.ModalTablePins
import RelCertifier.Verdicts.ModalCodePins
import RelCertifier.Trusted.Handoff

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse

/-- The modal phase owes one query group per component; a successful rebuild has exactly
`order.length` groups. -/
theorem packQueries_length (r : PackV2) {qss : List (List (IForm r.dim))}
    (h : packQueries r = some qss) : qss.length = r.order.length := by
  unfold packQueries modalVerdXQueries at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  simp

set_option maxRecDepth 100000 in
theorem derivedModalV2_eq : (packsV2.map (fun r => r.order.length)).sum = expectedModalV2 := by
  decide

/-- The reposition phase owes one query per component. -/
theorem dynPackQueries_length (r : DynPackV2) {qs : List (IForm r.dim)}
    (h : dynPackQueries r = some qs) : qs.length = r.order.length := by
  unfold dynPackQueries modalVerdDynXQueries at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  simp

set_option maxRecDepth 100000 in
theorem derivedDynV2_eq : (dynPacksV2.map (fun r => r.order.length)).sum = expectedDynV2 := by
  decide

theorem derivedHandoffV2_eq :
    (benchIRTableV2.map (fun r => RelCertifier.Handoff.declaredTransitions r.2)).sum
      = expectedHandoffV2 := by
  decide

theorem derivedPrunedV2_eq : prunedEdgesV2.length = expectedPrunedEdgesV2 := by decide

theorem derivedNonConnV2_eq : 2 * expectedPrunedEdgesV2 = expectedNonConnV2 := by decide

theorem suiteV2_size : benchIRTableV2.length = expectedSuiteV2.paths := by decide

/-- The declared right-mode count of the strict well-formedness gate IS the suite's: the
right modes of the 45 IR literals. -/
theorem suiteV2_wfModes :
    (benchIRTableV2.map (fun r => r.2.R.modes.length)).sum = expectedSuiteV2.wfModes := by
  decide

/-- The copied benchmarks' legacy packs: the legacy derivation, over the filtered table. -/
def derivedSameModalV2 : ℕ :=
  sameModalTable.foldl (fun acc r =>
    let (spec, info, order) := r
    let heads := (if info.ceilCo.isSome then 1 else 0)
               + (if info.region.isSome then 1 else 0)
               + (if info.tailCo.isSome then 1 else 0)
    acc + (RelCertifier.Verdicts.modalPairs spec info).length * (order.length + heads)) 0

theorem derivedSameModalV2_eq : derivedSameModalV2 = expectedSameModalV2 := by decide

/-- **Every pack queries the window's own row.** For every joint pack and every reposition
pack, the invariant row the runner quotes (`invRow`) is the row the tool reads for the
window's left mode, by name (`Handoff.invRowOf`, the same lookup as `certifyWithData`). Several
replays quote row 0 for every window of a benchmark whose rows are syntactically equal; this
pins that choice to the tool's lookup. -/
set_option maxRecDepth 100000 in
theorem packsV2_rowOfWindow :
    packsV2.all (fun r => decide (Handoff.invRowOf (irV2 r.bench)
      ((irV2 r.bench).L.modes.getD r.l ⟨"", [], .tt, .tt, []⟩)
        = some ((irV2 r.bench).invariants.getD r.invRow ("", PForm.tt)).2)) = true := by decide

set_option maxRecDepth 100000 in
theorem dynPacksV2_rowOfWindow :
    dynPacksV2.all (fun r => decide (Handoff.invRowOf (irV2 r.bench)
      ((irV2 r.bench).L.modes.getD r.l ⟨"", [], .tt, .tt, []⟩)
        = some ((irV2 r.bench).invariants.getD r.invRow ("", PForm.tt)).2)) = true := by decide

end RelCertifier.VerdictsV2

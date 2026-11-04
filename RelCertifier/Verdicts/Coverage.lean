/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Declared coverage: how many hypotheses a green run must actually discharge

A runner can issue fewer queries than it owes and still print only green lines: a pack
whose mode-pair list comes out empty runs its loop body zero times, a row that rebuilds
one component where nine are owed sends three queries instead of twenty-seven. Such a
run looks identical to a complete one.

So every phase's count is declared and checked. `counted` is called at each discharge
point (a query that came back `unsat`); `Main.runAllVerdictsV2` (`--run-verdicts-v2`,
`--check-quick-v2`) reads `dischargedCount` around each phase and compares the difference
against the phase's declared total with `checkPhase`, failing the run on any mismatch, low
*or* high. The bridge, reposition-progress and refutation runners (`VerdictsV2/RunBridge`,
`RunProgress`, `RunRefute`) do the same for their groups. The declared totals live next to
their tables (`VerdictsV2/RunV2.lean`, `RunBridge.lean`, `RunProgress.lean`,
`InstancesV2/Refute/Table.lean`).
-/

namespace RelCertifier.Verdicts

/-- Hypotheses discharged so far this process. -/
initialize dischargedCount : IO.Ref Nat ← IO.mkRef 0

/-- Record one discharged hypothesis. Call at the point a query came back `unsat`. -/
def counted : IO Unit := dischargedCount.modify (· + 1)

/-- Compare an actual phase count against its declared total, reporting either way. -/
def checkPhase (name : String) (actual want : Nat) : IO Bool := do
  if actual == want then
    IO.println s!"  [coverage] {name}: {actual}/{want} hypotheses discharged"
    return true
  else
    IO.eprintln s!"  [coverage] {name}: discharged {actual} but owes {want} — \
{if actual < want then "queries were skipped" else "unexpected extra queries"}; \
if this change is intended, update the declared count in `VerdictsV2/RunV2.lean`"
    return false

end RelCertifier.Verdicts

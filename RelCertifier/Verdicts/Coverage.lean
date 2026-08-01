/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Declared coverage — how many hypotheses a green run must actually discharge

Three times on 2026-07-31 a runner reported success for work it had not done:

* `rover_drag`'s pack produced an empty mode-pair list, so its loop body never ran and
  the pack "passed" having issued **no** query;
* `rover_rung2c` rebuilt one component at the wrong mode pair instead of nine at the
  right one — 3 queries where 27 were owed;
* `rover3tier_rung12`'s Accel row dropped a component — 1 query per pair instead of 2.

Every one of them printed green. Each was found by hand, and each fix was a patch to
the specific case. What they have in common is not the specific field that was wrong:
it is that **a run can issue fewer queries than it owes and still look identical to one
that issued them all**. Guarding each site individually does not stop the next one.

So the count is declared here and checked. `counted` is called at each discharge point;
`main`'s `--run-verdicts` compares the per-phase totals against `expected` and fails the
run on any mismatch, low *or* high. All three defects above would have tripped this
immediately, without anyone knowing to look for them.

**When the suite legitimately changes**, these numbers must be edited deliberately, and
the edit says exactly how coverage moved. That is the point: coverage cannot drift
quietly, in either direction.
-/

namespace RelCertifier.Verdicts

/-- Hypotheses discharged so far this process. -/
initialize dischargedCount : IO.Ref Nat ← IO.mkRef 0

/-- Record one discharged hypothesis. Call at the point a query came back `unsat`. -/
def counted : IO Unit := dischargedCount.modify (· + 1)

/-- What a complete `--run-verdicts` owes, per phase.

* `watertank` — 6: three routes over the six (window, right-mode) pairs it asserts.
* `cut` — 105: per-atom O2 route probes across the 13 cut-reliant benchmarks.
* `modal` — 483: every modal instance's verdict pack, one query per component per
  asserted mode pair. -/
structure Expected where
  watertank : Nat
  cut       : Nat
  modal     : Nat
  deriving Repr

/-- Measured 2026-07-31. Edit deliberately when the suite changes; see the module
docstring for why this is a declared constant rather than whatever the run produced. -/
def expected : Expected := { watertank := 6, cut := 105, modal := 483 }

/-- Compare an actual phase count against its declared total, reporting either way. -/
def checkPhase (name : String) (actual want : Nat) : IO Bool := do
  if actual == want then
    IO.println s!"  [coverage] {name}: {actual}/{want} hypotheses discharged"
    return true
  else
    IO.eprintln s!"  [coverage] {name}: discharged {actual} but owes {want} — \
{if actual < want then "queries were skipped" else "unexpected extra queries"}; \
if this change is intended, update `Verdicts/Coverage.expected`"
    return false

end RelCertifier.Verdicts

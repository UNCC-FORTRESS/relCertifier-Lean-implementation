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
* `modal` — 522: every modal instance's verdict pack, one query per component per
  asserted mode pair (483 for the 42 base packs, plus 39 for the five packs of the
  mode-keyed instances in `Instances/*Handoff.lean`).
* `handoff` — one static query per declared LEFT transition of every certified
  benchmark (self-loops included), `φ_inv(m') ∧ evolve_{m'} ∧ guard_m ∧ evolve_R ∧
  ¬φ_inv(m)` (domain-conditioned) — the cross-mode
  handoff of the mode-keyed invariant (`Trusted/Handoff.lean`). Mode-independent
  invariants make these vacuous; they are still issued and counted. -/
structure Expected where
  watertank : Nat
  cut       : Nat
  modal     : Nat
  handoff   : Nat
  deriving Repr

/-- Measured 2026-07-31 (watertank/cut/modal) and 2026-10-07 (handoff). Edit
deliberately when the suite changes; see the module docstring for why this is a
declared constant rather than whatever the run produced. -/
def expected : Expected := { watertank := 6, cut := 105, modal := 522, handoff := 215 }

/-- The handoff transitions that are KNOWN to fail, declared as `(benchmark, m', m)`.
A green handoff phase has exactly this failure set — a new failure fails the run, and so
does a declared failure that stops failing (the declaration is then stale). The one
entry is `rover3tier_rung12`'s `ACCEL → COAST` (0 → 1): its ACCEL row
(`v_L ≤ v_R + 0.5 ∧ a_L ≤ a_R + 0.8`) allows more slack on `3v + a` than its COAST row
(`3v_L + a_L ≤ 3v_R + 1.2`) admits, even inside the evolve domains, so the mode-keyed
invariant is not established across that switch (`COAST → ACCEL` holds under the
domain-conditioned query); see `docs/HANDOFF.md` for the countermodel. -/
def expectedHandoffFailures : List (String × Nat × Nat) :=
  [("rover3tier_rung12", 0, 1)]

/-- What a certification run over the standard suite produces.

`shield_unreachable` is the 47th benchmark and is *documented* to come back with an
inconclusive Z3 verdict rather than a decision — so a green run has exactly one error,
not zero. Declaring that here means a *second* benchmark starting to error is a failure
instead of blending into an expected one. -/
structure ExpectedSuite where
  paths     : Nat := 47
  certified : Nat := 46
  declined  : Nat := 0
  errors    : Nat := 1
  deriving Repr

def expectedSuite : ExpectedSuite := {}

/-- Compare a certification tally against `expectedSuite`.

Enforced only when the run covered the declared number of paths; on any other path set
the tally is reported but not judged, since the expected numbers describe the whole
suite and say nothing about a subset. -/
def checkSuite (nPaths certified declined errors : Nat) : IO Bool := do
  let e := expectedSuite
  if nPaths != e.paths then
    IO.println s!"  [suite] {certified} certified, {declined} declined, {errors} error(s) \
over {nPaths} path(s) — tally not enforced (the declared suite is {e.paths} paths)"
    return true
  else if certified == e.certified && declined == e.declined && errors == e.errors then
    IO.println s!"  [suite] {certified} certified, {declined} declined, {errors} error(s) \
— matches the declared suite"
    return true
  else
    IO.eprintln s!"  [suite] {certified} certified, {declined} declined, {errors} error(s) \
but the declared suite is {e.certified}/{e.declined}/{e.errors}; if this change is \
intended, update `Verdicts/Coverage.expectedSuite`"
    return false

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

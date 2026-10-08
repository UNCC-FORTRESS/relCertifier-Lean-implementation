# Benchmark suite

One directory per benchmark under `suite_uniform/`; `input.txt` is the complete
specification. **41 directories: 40 certified, plus `shield_unreachable`, which the tool
DECLINES (its `Shield` guard is a closed compound band the non-connection certificate
does not prune, and `Shield` is an admissible initial mode; it is outside the certified
suite).** Every certified benchmark carries a machine-checked modal Theorem 3 — see
`docs/CERTIFICATION-CHECK.md` for how to verify that end to end. `match_multi_rate`
declares a pruned stall fallback (`STALL`, edge `DRIVE → STALL`) that exercises the
non-connection certificate: `RELCERT_NO_PRUNE=1` makes it DECLINE (`docs/PRUNING.md`).

## The redesigned suite — `suite_v2/` (2026-10-08, branch `suite-redesign`)

`suite_v2/` is the redesigned 40-benchmark suite: the 19 kept benchmarks (terrain/
position ladder, story ladders, watertank) and `match_multi_rate`, `rover3tier_rung12`
copied unchanged, plus 19 new benchmarks in six families (ACC under sensor spoofing /
retune, quadrotor climb with a lighter airframe, battery charger, platoon follower with
a delayed link, rover patrol zones, arm with a leading reference). Each new file's
header states the physical story, units, the measured cover and the mechanisms it
exercises (`# scenario:` / `# mechanisms:` lines). The mechanism matrix, the per-family
design, the counter-runs and the scenarios tried and dropped are in
`docs/SUITE-REDESIGN.md`; `scripts/suite_v2_matrix.py` regenerates all of it. The Lean
instances still read `suite_uniform/` (the mechanization of `suite_v2` is a separate
task), so `suite_uniform/` must not be edited.

## File format

INI-style sections. The parser is `RelCertifier/Trusted/Parse.lean` and it is **strict**:
it rejects rather than weakens, and the CLI additionally refuses unknown keys and unknown
sections (`Trusted/KeyAudit.lean`, the W6 gate). Lines starting with `#` are comments.

```ini
[problem]
name       = watertank
max_depth  = 6           # accepted, deliberately unread by the parser (see note below)
lambda_min = 1.0
lambda_max = 10.0
bound_T    = 40.0        # optional

[Lsys]                   # the ideal system; [Rsys] is the implementation
state_vars = [x]
epsilon    = 1.0

[Lsys.mode.Low]          # one section per mode, named [<Lsys|Rsys>.mode.<Name>]
ode    = x' = smt2:(* 3 (- 0.6 (* x 0.04)));
guard  = x >= 0.0 and x < 13.0
evolve = x >= 0.0 and x <= 25.0
next   = [Mid, Low]

[relational_invariant]   # one row per LEFT mode name
Low  = x[l] <= x[r] + 3
Mid  = x[l] <= x[r] + 3
High = x[l] <= x[r] + 3
```

Key points, each of which the parser enforces:

* **`ode`** (singular) holds the whole vector field as one `;`-separated list:
  `ode = px' = vx; py' = vy; vx' = 0.2; vy' = 0;`. A right-hand side is either infix
  arithmetic or an `smt2:`-prefixed S-expression for anything nonlinear
  (`vx' = smt2:(* -0.5 vx)`).
* **`guard`** is the mode's entry condition, **`evolve`** the domain the flow may not
  leave, **`next`** the declared successors (the automaton's transition relation — the
  successor-completeness assumption in the repository README's trust table quantifies over
  exactly this list).
* **`state_vars`** is per system; both sides normally use the same names, and the
  coordinate *order* here is the order the Lean instances index by (`Lv 0`, `Rv 0`, …).
  A right-only variable (declared in `[Rsys]` only) is accepted: it gets a coordinate
  after the left variables, held fixed on the left (`shield_unreachable`'s `w`).
* **`[relational_invariant]`** has one row per **left** mode, over `[l]`/`[r]`-suffixed
  variables. Rows may differ per mode (nested tolerances are common: `Drive` tighter than
  `Drift` tighter than `Stop`); when they do, a single-invariant modal statement uses the
  weakest declared row, and where the rows have genuinely different *shapes* the instance
  states one theorem per left mode (`rover3tier_rung12`).
* **`lambda_min`/`lambda_max`** bound the time-stretch the right side may use when
  responding.

**Note on `max_depth`.** Every input carries it and the parser deliberately never reads
it — search depth is a tool parameter, not part of the specification. The key is
whitelisted (rather than silently dropped) precisely so that the CLI's key audit can still
reject genuinely unknown keys. The underlying observation is recorded in
`docs/COVER-AUDIT.md`.

## Running one

```bash
lake build relcert
./.lake/build/bin/relcert benchmarks/suite_uniform/watertank/input.txt
```

The tool parses, lowers, searches for a cover, and discharges the analytic side conditions
with Z3. Certified data is emitted into `RelCertifier/Instances/BenchIR/<name>.lean`,
`BenchCovers/<name>.lean`, and friends — drift-checked literals from which the
per-benchmark theorem instances are built. `./.lake/build/bin/relcert-test` re-parses every
`input.txt` and checks it still equals the emitted literal, so a benchmark file and its
theorem cannot drift apart silently.

## The suite

watertank; the arm chain / arm fidelity families (the plant-fan copies and `arm_refinement`, byte-identical duplicates, were removed on 2026-10-08 — `docs/SUITE-DEDUPE.md`); rover refinement ladders
(2–12 dof); dof-terrain rungs; endurance, attitude, lateral and rollover stories; plus the
rover tier, coupled, position and drag models. Sizes run from 1 to 12 state variables per
side.

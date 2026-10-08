# Verdict-hypothesis evidence audit — 2026-07-31

> **Note (2026-10-08).** This audit was performed on the 46-benchmark suite. `arm_fidelity_high`, `plant_fan_high`, `arm_refinement`, `plant_fan_low`, `match_multi_eps` and `plant_fan_mid` were removed as duplicates afterwards (`SUITE-DEDUPE.md`); rows naming them describe the suite as it was.

**Question this document answers.** 41 of the 47 modal theorems carry named Z3 verdict
hypotheses (`Verd… l m`). A theorem with a false hypothesis is vacuously true, and
`#print axioms` cannot detect that. So: what justifies believing those hypotheses?

**Answer, as of the end of 2026-07-31.** All of them are re-run, in one route, by
`relcert --run-verdicts` — 594 queries, all `unsat`, exit 0 — and the query the runner
sends is tied to the query the theorem assumes by kernel pins
(`Verdicts/ModalPinTable.lean`, `ModalTablePins.lean`, `ModalCodePins.lean` — the last
covering the runner's *code*, not just its data). Six hypotheses were
found **vacuous** during the day's audit and all six were repaired; four further defects
were found in the runner's own table, three of them by the pins. What remains outside the
kernel is listed under *The last unpinned link* below, and is narrow.

**How to read this document.** It was written in three passes over one day and the early
sections describe a weaker situation than the later ones:

| § | pass | status |
|---|---|---|
| 1–6 | containment argument: the hypotheses are *implied* by queries the tool ran | **superseded, and moved** to `archive/CONTAINMENT-AUDIT-2026-07-31.md`. It was the justification while the runner still covered only watertank's 6 and the 105 cut probes. |
| Part II | the hypothesis-truth audit: six vacuous theorems, and their repair | current |
| *The last unpinned link* | the runner's table, and how it is tied to the theorems | current |

§§1–6 are history and now live in `archive/`. The live claim is in the last two.

---

---

## 1–6. The containment argument — moved

The morning's justification (the hypotheses are *implied* by queries the tool already
ran, via a domain-containment argument checked over the emitted covers) lives in
[`archive/CONTAINMENT-AUDIT-2026-07-31.md`](archive/CONTAINMENT-AUDIT-2026-07-31.md).

It is **superseded** — the hypotheses now rest on the runner re-running all 594 queries
against pinned identities, not on that argument — and is kept only as a record of what
was checked, plus the two false alarms in its §4, which are traps worth not repeating.

---

# PART II — Complete hypothesis-truth audit (2026-07-31, later the same day)

Part I asked whether the *evidence* for each hypothesis was sound. It did not ask
the prior question: **is each hypothesis actually true?** This part does, for all
42 `Verd` definitions across the 41 instances that carry them.

## Method

For each instance, two steps:

1. **Pin.** Prove `VerdX … = <a query built only from the benchmark IR and data>`
   by `rfl`. The kernel then certifies that the query being tested IS the theorem's
   own hypothesis. All 42 pins prove. This is what makes the result trustworthy —
   four earlier reconstruction attempts produced false alarms precisely because
   they lacked this step (see the false alarms in
   [`archive/CONTAINMENT-AUDIT-2026-07-31.md`](archive/CONTAINMENT-AUDIT-2026-07-31.md) §4).
2. **Run.** Send all three routes (`flowQuery`, `…Strict`, `…Superlevel`) to Z3.
   `Verd` is a disjunction, so the hypothesis holds iff *some* route is `unsat`.

## Result — 6 vacuous theorems

| instance | failing pairs | all three routes | cause |
|---|---|---|---|
| `endurance_orderlift_1to2` | (l, STEEP) ∀l | SAT | asserted pairs the cover never certified (∀-quantified hypothesis) |
| `arm_chain_rung3` | (l, Hold) ∀l | SAT | domain omits the `Hold` guard/cut `theta ≥ 0.6` |
| `arm_fidelity_high` | (l, Hold) ∀l | SAT | same |
| `plant_fan_high` | (l, Hold) ∀l | SAT | same |
| `arm_fidelity_mid` | (l, Hold) ∀l | SAT | same |
| `plant_fan_mid` | (l, Hold) ∀l | SAT | same |

All other instances pass at every asserted index, including all 7 ceiling-shaped
ones (37 query-groups) and the two special shapes (`rover_drag`, `rung2c`).

**The benchmarks are not in question.** The tool holds a valid certificate for each
— for the five `Hold` cases it certifies at the *narrowed* domain, which the cover
records as `jointOK = true`. What is wrong is the **theorem statement**: it asserts
the query over the bare evolve domain, which is strictly harder and false. A false
hypothesis makes the theorem vacuously true, so it delivers nothing — and this is
invisible to `#print axioms`, which is why it survived.

Measured confirmation of the diagnosis, all 10 `Hold` pairs:

```
stated (bare domain)   : A=SAT  B=SAT  C=SAT
+ Hold cut theta ≥ 0.6 : A=SAT  B=unsat C=unsat
```

## Why the fix is principled, not a patch

`theta ≥ 0.6` is exactly the `Hold` mode's **guard**. The trust base already
assumes *guard-gated switching*: at a mode change the entering mode's guard holds.
The settling and throughout families carry that guard **in the statement** (`Gd`);
the modal family does not, and these five are where the omission bites. Restating
the domain as `domL ∧ domR ∧ guard_R(m)` writes down what the contract already
grants.

## Status — ALL SIX REPAIRED (2026-07-31)

| instance | repair | commit |
|---|---|---|
| `endurance_orderlift_1to2` | hypothesis narrowed to the six certified pairs | `edf54d5` |
| `arm_chain_rung3` | `Hold` region added as an invariant component | `e62cb5a` |
| `arm_fidelity_high`, `plant_fan_high` | same | `597def5` |
| `arm_fidelity_mid`, `plant_fan_mid` | same (region via route C — their `Hold` is asymptotic, not frozen) | `28c86f2` |

Each verified four ways: compiles; axioms unchanged; the new `Verd` pinned by `rfl`
to a data-built query; that query measured `unsat`. Then re-verified independently
with freshly written pins and queries — 6/6 pins, 16/16 Z3 query-groups, full build
green, 47 theorems audited (42 + `z3_unsat_sound`, 5 standard-three, zero `sorryAx`).

`ModalSpecs` refused to compile when the five statements changed, flagging exactly
those five — the spec layer working as designed (`e56b8a6`).

### Superseded status note

The five `Hold` cases were, before the repair, — the repair needs the guard threaded through the modal
coupling, for which the machinery exists (`CutCover`'s `RightReachG`,
`GuardThreaded.lean`) but is not yet wired to the modal chain.

Until then, **six of the 47 modal theorems say nothing about their benchmark**, and
the suite claim should be read as 41 of 47 meaningful (46 with `endurance` fixed,
less the five outstanding).

## Fix design for the five `Hold` cases (implemented — see *Status* above)

The repair is the **mode-region** device the repo already uses for
`refinement_ladder_rover_rung2c_6dof` — not new theory. Every piece exists:

| piece | where |
|---|---|
| `lowFace b sr` — the region term `b − s_R` (region = `b ≤ s_R`) | `Proofs/Encoding/ModeRegion.lean:36` |
| `lowR_preserved` — region survives a run, from a `SegPreservesOn` certificate | `ModeRegion.lean:46` |
| `theorem3_faithful_multiR_LR` + `mvRegionR` — the top theorem carrying regions | `Proofs/Encoding/EnvelopeChainR.lean` |
| a worked instance | `Instances/RoverRung2cModal.lean` (threads `lowFace (b6 l) (Rv 1)` as a ninth invariant conjunct) |

**Per instance:**

1. add the region component `lowFace (3/5) (Rv 0)` — i.e. `theta_R ≥ 0.6`, exactly
   `Hold`'s guard — to the invariant component list;
2. restate `Verd` in the multi-component strata form so the region narrows the
   later components' domains (measured: this makes routes B and C `unsat`);
3. discharge region preservation. **`Hold`'s field is `theta' = 0`** — the
   coordinate is frozen, so the region is trivially invariant; this is the easiest
   possible case of `lowR_preserved`;
4. switch the top theorem from the `multiE`/`multiF` form to
   `theorem3_faithful_multiR_LR` with `mvRegionR`, and thread the region through
   the coupling and `Hmulti` dispatch.

Steps 1–3 are small. **Step 4 is the work**: it converts a single-component
`multiE` instance into a region-carrying `multiR` one, and `RoverRung2cModal.lean`
— the only existing example — is ~1500 lines. Budget a session per instance for
the first, then the remaining four are near-clones (same family, same `Hold`,
identical guard `theta ≥ 0.6`, all frozen).

**Do not shortcut it** by putting the guard directly into the response program's
domain: that would change the automaton in the statement and stop matching the
benchmark. The region device is the faithful route, which is why `rung2c` uses it.

---

## The last unpinned link (closed, 2026-07-31)

`relcert --run-verdicts` discharges **every** theorem's hypotheses in one route
(594 queries: 6 watertank + 105 cut probes + 483 modal). All three links from *what
Z3 is asked* to *what the theorem assumes* are now kernel-checked:

| link | status |
|---|---|
| spec's argument pairs → theorem | `ModalSpecs.modal_from_spec` ✓ |
| `RunModal`'s `RunInfo` data → the instance's actual query | `Verdicts/ModalPinTable` ✓ |
| IR query shape → host query shape | `Verdicts/ModalPins` ✓ |

`RunInfo` (dimension, invariant row, λ, component order, region and ceiling heads) is
still hand-written in `RunModal.modalTable`, but it is no longer unchecked: each of
the 42 verdict packs carries a

    theorem pin_X (l m : ℕ) : VerdX l m = modalVerd <IR> <fields…> l m := pin_of rfl

in `Verdicts/ModalPinTable.lean`, where `modalVerd` states at the host level exactly
what the runner builds. A wrong field no longer type-checks. Eleven instances state
their hypothesis as a bare three-route disjunction rather than a `∀` over components;
those use `modalVerd1`, with a companion `modalComps … = [modalRowG …]` pin so the
runner's one-element component list is provably that same row.

**What the pins caught.** Three further wrong entries, of a kind the earlier hand-audits
had missed four times over. Every one had been reported green.

1. **`rover_rung2c` — wrong mode pair and a missing component list.** It runs left mode
   `l` against right mode `l`, not against a fixed `0`, and carries eight invariant
   components plus a tail region face — where the table said *one* component at `(0, l)`.
   `RunInfo` had no tail-append field at all. `RunInfo` gains
   `tailCo`/`tailFlip`/`tailKs` mirroring the ceiling head; the corrected entry rebuilds
   27 queries where it used to rebuild 3.
2. **`rover3tier_rung12` (Accel row) — a dropped component.** The table passed `order :=
   [0]` for a theorem whose hypothesis ranges over two components, so component 1 was
   never checked for either asserted pair. The spec's own `order` field already said
   `[0, 1]`, and `spec_components` proves it; only the runner's copy was wrong. The same
   row also cited `Coast`'s spec for data belonging to `Accel`'s theorem — the rebuilt
   queries were identical, but the provenance link pointed at the wrong theorem.
3. **`rover_drag` — checked zero times.** Its spec is `nullary := true` with no `pairs`
   and no `singles`, so the runner's `pairs` list came out empty, the per-pair loop body
   never ran, and `runSpec` returned success having issued no query at all. The pack
   printed nothing and the run still reported `ALL MODAL HYPOTHESES DISCHARGED`. This is
   the worst of the three: not a wrong query, but *no* query, passing silently. The
   runner now maps a nullary `Verd` to the single pair `(0, 0)` that `pin_RoverDrag`
   names, and — independently of that case — treats an empty `pairs` list as `SKIP` and
   a non-green run, so an unchecked pack can no longer masquerade as a discharged one.

All 594 queries return `unsat` after the corrections.

**How the table itself is tied.** `ModalPinTable` proves `VerdX = modalVerd …` against
the *instance*, by `rfl`. For that to say anything about the runner, its arguments have
to be the runner's, so:

* `dim`, `invRow` and `order` are **quoted straight out of the row** —
  `modalVerd IR (row 27).2.1.dim (row 27).2.1.invRow (row 27).2.2 …` — so those three
  fields exist in exactly one place. Edit the table and the pin stops compiling.
* the remaining fields are pinned as data in `Verdicts/ModalTablePins.lean`, one
  `rfl` theorem per row, including `(row i).1.bench` so that a wrong *row index* in a
  pin fails to compile rather than silently pinning a different benchmark;
* the `(left, right)` pairs are pinned through `RunModal.modalPairs` — the runner's own
  function, factored out of `runSpec` for this purpose rather than transcribed, since a
  theorem about a copy would not constrain the runner.

Checked by deliberately corrupting the table (2026-07-31): a wrong `tailCo`, a dropped
`order` entry, and a wrong `fixedOther` each fail the build. Those are exactly the three
defect classes found above.

**The runner's code, not just its data.** The pins above tie the `RunInfo` row to the
theorems, which still left the code turning those fields into a query read rather than
proved. `Verdicts/ModalCodePins.lean` closes that, in 72 `rfl`/`simp` theorems over the
functions `runSpec` and `checkComp` actually call:

* `modalLamI` — that the pair `(lamN, lamD)` denotes the real number `lamN/lamD`. This
  was the sharpest remaining hole: no data pin mentioned those fields, so changing the
  `/` to a `*` left every pin compiling, and since a larger λ is a *weaker* flow
  condition the wrong query would likely still come back `unsat`. Now 12 theorems fail
  if that line changes.
* `modalHeadI` — that `ceilCo`/`ceilFlip`/`ceilKs` build the head term the instance
  names (`ceilR m` and friends), and likewise `rover_rung2c`'s tail face. Stated per
  right mode, because `List.getD` does not reduce at a variable index.
* `modalRoutes` — that the three queries tried per component denote exactly
  `flowQuery`, `flowQueryStrict` and `flowQuerySuperlevel`, the three the hypotheses
  disjoin. Generic in every argument.

Checked by breaking the runner three ways: `/` → `*` in the λ fails 12 theorems,
dropping route C fails 3, and shifting the head coordinate by one fails 24. Before this
file, all three edits compiled clean.

So the chain is now kernel-checked from a theorem's `Verd…` all the way to the IR query
handed to `toScript`. What remains outside the kernel is the printer and Z3 — the frozen
trust base — plus one control-flow fact left to reading: that `checkComp`'s loop reports
success exactly when one of the three routes answered `unsat`.

**On the earlier diagnosis.** This section previously recorded that the composite
`VerdX = modalVerd` failed `rfl` while each step reduced, and guessed the unifier was
at fault. That was wrong. The scratch file exercising the pin lacked
`open RelCertifier.Parse`, so the benchmark's IR name was unresolvable — and because
`lake env lean` does not apply the lakefile's `leanOptions`, `autoImplicit`
silently bound it as a fresh universally-quantified variable. The pin was stating
something about an *arbitrary* `PProblem`, so `rfl` failed for an entirely mundane
reason. In-repo files are not exposed to this: the lakefile sets
`relaxedAutoImplicit = false`, which rejects multi-character auto-binding, and
`ModalPinTable` additionally sets `autoImplicit false`. Worth recording because the
failure mode is invisible in the error message — it reports a defeq failure, not an
unknown identifier — and because an auto-bound pin that *did* happen to prove would
have been worthless while looking fine.

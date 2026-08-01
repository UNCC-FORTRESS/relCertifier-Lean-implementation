# Verdict-hypothesis evidence audit — 2026-07-31

**Question this document answers.** 41 of the 47 modal theorems carry named Z3
verdict hypotheses (`Verd… l m`) that are *not* re-run by `relcert --run-verdicts`
and have no kernel identity theorems tying them to the runner
(`docs/CERTIFICATION-CHECK.md` § "What is measured but not yet in the runner").
What, exactly, justifies believing those hypotheses — and how solid is that
justification?

**Answer, up front.** Every asserted hypothesis is implied by queries the tool
demonstrably ran and got `unsat` on, via a domain-containment argument that was
checked exhaustively (210/210 non-trivial cases) on 2026-07-31 against the emitted
cover data at commit `f0858b6`. Nothing is broken and nothing was found unverified.
The caveat: the containment argument itself lives in this document and its script —
it is **not** kernel-checked and **not** part of any automated test. This document
is the record of that argument, its scope, and its expiry conditions.

---

## 1. Background: what the hypotheses say, and what the tool did

A verdict hypothesis has the shape (e.g. `VerdE` in `RoverLadderRung1Modal.lean`):

```lean
def VerdE (l m : ℕ) : Prop :=
  ∀ i (hi : i < (gE :: gsE).length),
    z3solve (flowQuery ⟨(gE :: gsE)[i], fLE l, fRE m, Term.const 1,
      strataDomHost (Formula.and domLE domRE) ((gE :: gsE).take i)⟩) = unsat ∨ …
```

Component `i`'s query domain is narrowed by the **prefix** `(g :: gs).take i` of the
instance's component list — the stratified differential-cut discipline (a component
may assume only previously-proven components; the mutual form was the R4 unsoundness).

The tool's search (`checkSeg`, `Trusted/OracleAPI.lean`) runs the same stratified
fixpoint **per (left mode, right mode) pair**, proving components in whatever order
that pair's dynamics allow, and emits the result as `PairStrataE.order`
(`Checker/CoverEmit.lean`), whose contract is:

> `order[k]` is the component index proven in round `k+1`; the flow-query domain of
> component `order[k]` is narrowed by exactly `order.take k`.

So there are two descriptions of "what was assumed while proving component `c`":
the statement's fixed prefix, and the tool's per-pair `order.take k`. They need not
be equal — and for 8 benchmarks they are not (different pairs even have different
orders within one benchmark; the orders are search output, not a design choice).

## 2. The containment principle

Narrowing a query's domain by *more* invariant components only shrinks the set of
candidate counterexamples, so **`unsat` is preserved when the assumption set grows**:

> If the tool proved component `c` for pair `(l,m)` assuming set `T = order.take k`,
> and the statement's prefix for `c` is `S = indices of (g::gs).take i`, then
> `T ⊆ S` implies the tool's `unsat` entails the statement's query being `unsat`.

This is the whole argument. It reduces "is the hypothesis justified?" to a finite,
purely combinatorial check over emitted data: *for every pair the theorem asserts,
for every component, is the tool's assumption set contained in the statement's
prefix?*

## 3. The audit and its results

Run 2026-07-31 against the emitted covers (`Instances/BenchCovers/*.lean`) and the
instance files at `f0858b6`; script in §6.

**Exposure classification (46 benchmarks):**

| class | count | exposure |
|---|---|---|
| single-component invariant (every order is `[0]`) | 27 | none — nothing to order |
| multi-component, all emitted orders are the identity | 11 | none — any prefix convention agrees |
| multi-component, some emitted order non-identity | 8 | needs the containment check |

The 8: `rung2_3to6`, `rung2c_6dof`, `rung3_6to8`, `rover_attitude_cone_12dof`,
`story2_lateral_rung_a/b`, `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`.
Four of them list their components *in the cover's DC order* (e.g. `gs6 = [gAt 2,
gAt 3, gAt 1]` matching emitted `[0,2,3,1]`); four list identity order while the
tool's order differs but is increasing.

**Containment over asserted pairs: 210 checks, 210 safe, 0 unsafe.**

**Coverage over asserted pairs:** every `(l,m)` pair named by a theorem's `hv`
binders has an emitted strata row — no hypothesis rests on a query the tool never
ran. (Checked for all instances with explicit `hv<l><m>` binders.)

## 4. Two false alarms during the audit — recorded so they are not repeated

The audit initially reported problems twice; both were errors in the audit, not in
the repository. They are exactly the traps a future auditor will hit:

1. **Unasserted pairs.** The emitted covers faithfully record *failed* joint
   attempts: e.g. `story3_rollover_base_12dof` left-FLAT rows carry the joint order
   `[4,2,3]` next to `jointOK = false` — that pair is covered by dynamic reposition
   certificates (identity order) instead, and **no theorem asserts it** (the
   theorem's binders are exactly the six `jointOK = true` pairs). Comparing
   statements against *all* emitted rows produces phantom violations. Restrict to
   the pairs the theorem's binders name.
2. **`hv` name collisions.** Instances name parse-pin lemmas `hv05 : parseRat "0.5" …`.
   A regex harvesting `hv<digits>` as verdict binders will invent hypotheses like
   `(0,5)` for 3-mode benchmarks. Match the theorem's binder list, not the file.

## 5. What this audit does and does not establish — and when it expires

Established: at `f0858b6`, every modal theorem's verdict hypotheses are entailed by
tool-executed `unsat` queries (re-runnable via
`./.lake/build/bin/relcert benchmarks/suite_uniform/*/input.txt`), through the §2
containment, checked exhaustively by the §6 script.

Not established, deliberately left open (the "options shelf" if ever needed):

* the containment check is **not** in `relcert-test` (option A: add it — hours);
* the §2 monotonicity fact is **not** a Lean lemma with a decidable per-benchmark
  side condition (option B: prove it — ~a day plus a world rebuild);
* `--run-verdicts` still re-runs only watertank's 6 + the 105 cut probes, not the
  41 instances' packs (option C: extend the runner — the operational gold standard).

**Expiry.** This audit is a statement about the *frozen* emitted covers. It goes
stale the moment any cover is regenerated (`--emit-cover` after a model or search
change): strata orders are search output and may legally change, and nothing in the
build will re-check containment. **If covers are ever regenerated, re-run §6 —**
or, better, take option A first.

## 6. Reproduction

```python
# containment audit over asserted pairs — run from the repo root
import re, glob, os
row  = re.compile(r'⟨"([A-Za-z0-9_]+)",\s*\[([0-9,\s]*)\]\s*,\s*\[([0-9,\s]*)\]\s*,\s*\[([0-9,\s]*)\]⟩')
row2 = re.compile(r'⟨"([A-Za-z0-9_]+)",\s*\[([0-9,\s]*)\]⟩')          # older 1-list shape
split = re.compile(r'⟨"([A-Za-z0-9_]+)",\s*\([^)]*\)\s*/\s*\d+,\s*\d+,')  # left-cover blocks
nums = lambda s: [int(x) for x in s.split(',') if x.strip()] if s and s.strip() else []

# instance component order = the gAt indices of `g := gAt h` and `gs := [gAt …]`
def inst_seq(txt):
    head = re.search(r'noncomputable def \w+ : Term \(Var \d+\) := gAt (\d+)', txt)
    tail = re.search(r'noncomputable def \w+ : List \(Term \(Var \d+\)\) :=\s*\n?\s*\[([^\]]*)\]', txt)
    if not head: return None
    return [int(head.group(1))] + [int(x) for x in re.findall(r'gAt\s+(\d+)', tail.group(1) if tail else '')]

safe = unsafe = 0
for cf in sorted(glob.glob('RelCertifier/Instances/BenchCovers/*.lean')):
    bench = os.path.basename(cf)[:-5]
    blocks = split.split(open(cf).read())[1:]
    rows = {}
    for li in range(0, len(blocks), 2):
        body = blocks[li+1] if li+1 < len(blocks) else ''
        for mi, m in enumerate(list(row.finditer(body)) or list(row2.finditer(body))):
            rows[(li//2, mi)] = nums(m.group(2))          # group(2) = the JOINT order
    for inst in glob.glob('RelCertifier/Instances/*Modal.lean'):
        itxt = open(inst).read()
        if f'BenchIR.{bench}\n' not in itxt and f'BenchIR.{bench} ' not in itxt: continue
        thm = re.search(r'theorem \w+_modal[^:]*?:', itxt, re.S)
        pairs = {(int(a), int(b)) for a, b in re.findall(r'hv(\d)(\d)\s*:\s*Verd', thm.group(0))} if thm else set()
        seq = inst_seq(itxt)
        if not seq: continue
        for (l, m), order in rows.items():
            if (l, m) not in pairs: continue              # §4 trap 1: asserted pairs only
            for k, c in enumerate(order):
                if c not in seq: continue
                if set(order[:k]) <= set(seq[:seq.index(c)]): safe += 1
                else: unsafe += 1; print('UNSAFE', bench, (l, m), order, 'component', c)
print(f'safe {safe}  unsafe {unsafe}')   # 2026-07-31 @ f0858b6: safe 210  unsafe 0
```

(The binder harvest above guards against §4 trap 2 by anchoring on `hv<l><m> : Verd`.
Instances whose verdict binders are not of that shape — e.g. per-mode `VerdR6 l` —
were checked by inspection; their component lists are in the cover's DC order.)

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
   they lacked this step (§4).
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

## Fix design for the five `Hold` cases (validated, not yet implemented)

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

**What is still not kernel-checked.** Two things, both narrow:

* **λ and the head terms.** A pin writes `(9 : ℝ) / 4`, `regA`, `ceilR m`; the table
  carries `lamN`/`lamD`, `region`, `ceilCo`/`ceilKs`. `ModalTablePins` pins the table
  side, but nothing in the kernel says `lamN/lamD` *means* `lamN/lamD : ℝ`, or that
  `ceilCo`/`ceilKs` build that head term — those are two short stretches of runner code,
  checked by reading. The numeric agreement between the two sides was checked by script
  over all 42 rows, not by eye: λ literals against `lamN`/`lamD`, fixed modes against the
  visited pairs, and the three `lamPerL` rows against the instances' own `lamC`/`lamD`/
  `lamM` (`5/2, 3/2, 1` etc.).
* **The `comps_*` shape argument.** For the eleven one-component instances,
  `modalComps … = [modalRowG …]` says the runner's component list is the single
  invariant row; that the runner's *loop over a one-element list* issues exactly the
  three queries of a bare disjunction is again read, not proved.

**Correction (measured 2026-07-31).** An earlier version of this paragraph blamed the
`ℕ → ℝ` cast: it claimed the table's λ reaches the host statement as
`((9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)`, which is not definitionally the instance's
`(9 : ℝ) / 4`. **That is false** — `((9:ℕ):ℝ)/((4:ℕ):ℝ) = (9:ℝ)/4` closes by `rfl`, as
does `((2:ℕ):ℝ) = (2:ℝ)`. The claim was asserted from a general worry about casts rather
than probed, and it named the wrong obstacle. What actually blocks a pin from quoting
the table row is two different things:

* **`List.getD` at a symbolic index.** `info.lamPerL.getD l …` and
  `info.ceilKs.getD m …` are stuck while `l`/`m` are variables, so neither λ (for the
  three `lamPerL` rows) nor a per-right-mode ceiling head reduces. At a *concrete*
  index it does reduce — `lamOf (row 0).2.1 0 = (5:ℝ)/2` closes by `rfl`.
* **Elaboration order, in one spot.** `Rv 1` in `rover_rung2c`'s tail wants
  `Fin (row 31).2.1.dim` before the projection reduces, so the numeral has no `OfNat`
  instance. A type ascription fixes it; it is not a defeq failure.

The structural fields carry no such obstacle: quoting `dim`, `invRow` and `order`
straight from the row closes by `rfl` for every shape in the table.

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

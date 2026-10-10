> **HISTORY (moved to `docs/history/` on 2026-10-10).** A superseded record, kept for
> provenance; `docs/history/README.md` says what replaced it. Paths, file names and counts
> below describe the repository at the time of writing, not the current artifact.

# Containment audit — 2026-07-31 morning (SUPERSEDED, kept as record)

> **This argument is no longer what the verdict hypotheses rest on.** It was the
> justification during the morning of 2026-07-31, while `--run-verdicts` still re-ran
> only watertank's 6 hypotheses and the 105 cut probes. By the end of that day the
> runner covered every pack — 594 queries, each pinned to the theorem that assumes it —
> and the hypotheses rest on *that*.
>
> Kept for two reasons: it records what was checked and how, and §4's two false alarms
> are traps a future auditor will hit again. **Do not cite §3's "210/210 safe" as
> current evidence.** Live status: [`../VERDICT-EVIDENCE-AUDIT.md`](../VERDICT-EVIDENCE-AUDIT.md).
>
> It is also frozen against the emitted covers at `f0858b6`. If any cover is regenerated
> (`--emit-cover` after a model or search change), strata orders may legally change and
> nothing re-checks this — but nothing depends on it either.

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
* ~~`--run-verdicts` re-runs only watertank's 6 + the 105 cut probes, not the 41
  instances' packs (option C: extend the runner — the operational gold standard)~~
  — **done later the same day.** The runner now covers every pack in one route,
  594 queries, and the containment argument of §§1–6 is no longer what the
  hypotheses rest on. See *The last unpinned link*.

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

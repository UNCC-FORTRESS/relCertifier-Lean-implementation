# Scope: supporting reset maps in the models

Status: SCOPING ONLY. Nothing implemented, nothing scheduled — the feature is
deferred by decision (2026-07-19). This document is the **reconciled** scoping: it
merges a read-only sweep done in this repo with an earlier, more detailed sweep done
from the QRC-paper thread (`relcertifier-handoff.md`, item B), which is now superseded
by this file. Companion reading: README ("The end-to-end guarantee, intuitively"),
`docs/COVER-AUDIT.md` (§ the unknown-key parser hole — a prerequisite, see §0),
`docs/FIXPOINT-DESIGN.md`.

---

## 0. Prerequisite: the parser silently drops unknown keys

**STATUS: FIXED (W6, commit `1bf8e30`).** This section is kept because it states the
prerequisite a reset feature still depends on, and because the shape of the fix
constrains where reset syntax may be added.

The hole as it stood: `Trusted/Parse.lean` is in the trust base and its stated
contract is *"the parser REJECTS, never weakens"*. It honoured that for malformed
input and even rejected one retired key by name (`strengthen`), but it **silently
ignored unknown keys** — `parseModeE` reads exactly `ode`, `guard`, `evolve`, `next`,
and anything else in a `[*.mode.*]` section was dropped. So writing
`reset = x2 := 1` into a mode section parsed cleanly and was discarded: a green
certification of a model that is not the one in the file.

The fix is `Trusted/KeyAudit.lean` — `auditKeys` (a per-section whitelist, with
`max_depth`/`bound_T` listed as known-but-unused) plus `readProblemStrict`, wired into
every CLI parse site in `Main.lean`. All 47 benchmark inputs pass the audit unchanged.

Measured on 2026-07-31 — the doc's own trigger case, `reset = x2 := 1` injected into
each mode section of `watertank/input.txt`:

```
ERROR [parse: line 84: unknown key 'reset'; line 91: unknown key 'reset'; …
       — the parser would silently drop these (W6 gate)]
errors=1                                          # exit 1
```

**The nuance that matters for a future reset feature:** `Trusted/Parse.lean` itself is
unchanged and still ignores unknown keys. The gate lives one level up, at the CLI
entry points. That was deliberate — `Parse.lean` sits upstream of the entire proof
layer, so touching it forces a world rebuild (measured at 10–14 hours; see the
rebuild-hygiene note in `docs/READING-GUIDE.md`). Consequence: adding reset syntax
means adding `reset` to the `KeyAudit` whitelist *and* teaching `parseModeE` to read
it — and any parse path that does not go through `readProblemStrict` is still
unguarded.

---

## 1. What a reset map is here, and what it buys

Today a mode switch changes **only the mode**: the state is continuous across the jump
(`Proofs/Encoding/JointBridge.lean:34`, and `Checker/Cover.lean` documents it —
"the continuous state is unchanged (`μ = ν`); only the mode advances").

**The model of interest** places a **per-target-mode** reset immediately before the flow:

```
( ⋃_{m ∈ modes}  ?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; x := ρ_m(x) ;
                 {x' = f_m(x) & evolC_m} )*
```

Two features drive everything below. The guard is the **target mode's**, tested at the
**pre-reset** state — so a reset can never enable a transition that was not already
enabled. And the reset sits **immediately before the flow** — so every mode residence
begins at a reset image.

(The earlier sweep assumed a **per-edge** `REdge.reset`. Per-target-mode is simpler and
is the model of record: obligations are |Q| not |E|, `PMode` gains one field rather than
`PEdge` being introduced, and `Faithful` extends along its existing per-mode grain.)

**What it buys the modeling story.** Benchmarks in the wild carry per-transition resets:
entry clamps (`x2 := 1`), reflections (`x1 := -x1`), translations (`x1 := x1 - 1.3`),
controller re-initialization, clock/timer resets, impacts. For this project's attack
narrative specifically: a sensor **spoof at switch time** rather than a continuous
drift. No benchmark in the suite uses resets today, so the feature is purely additive.

---

## 2. What is already free

1. **The object language already has assignments.** `Program.assign` and its whole dL
   metatheory (`dL-lean` `Syntax.lean:101`, `Semantics.lean:71`, `Calculus.lean:44,77`,
   `Static.lean:55,68,86`, `Coincidence.lean:110`). No new dL work.

2. **The top-level theorem statement needs zero change.** `theorem3Form` takes arbitrary
   programs (`Checker/Cover/Encoding.lean:51`); a reset-carrying automaton is just a
   different `R`. Encoding soundness is untouched.

3. **The decision procedure is state-free.** `decideCovered` (`Checker/Checker.lean:48`)
   walks `⟨q, B, σ⟩` consulting only per-mode flags, never a state. The combinatorial
   search, `decideCovered_sound`, and every `by decide` replay keep working verbatim.

4. **The printer should not need to change.** The obligation is a substitution performed
   at the IR level, printed with the existing term grammar. (Verify early; keeping
   `toScript` untouched is worth real money.)

5. **A direct template already exists.** `mv := e.tgt` inside `modeStep`, with
   `modeStep_sem` and the framing lemma `sem_ode_frame_upd`
   (`JointBridge.lean:38,96,72`) — *an assignment on a declared transition, proved
   sound*. That is the shape a state reset needs.

6. **The best single reuse for the obligation**: `regionUnsat` (`OracleAPI.lean:206-221`)
   with its kernel connector `regionInv_of_unsat` (`Cover.lean:368-374`) — a static,
   ODE-free Z3 obligation under UNSAT-only discipline. The jump obligation has exactly
   this shape.

**Do not be misled by names.** `ClockReduce.lean` and `RepositionDischarge.lean` both
speak of "reset state", but both hinge on the reset touching a coordinate the invariant
*ignores* (the `tg := 0` clock reset is an encoding-internal device on a *fresh*
coordinate, later eliminated by `clockReduce`; `ClockedTop.lean` is DEPRECATED besides).
A real reset writes a coordinate the invariant depends on, so those arguments break —
only the proof idiom transfers.

---

## 3. What changes, layer by layer

### 3.1 Surface syntax, IR, tool

- `PMode` (`Trusted/Parse.lean:54`) gains `reset : List (String × PExpr) := []`. **Give
  it a Lean default**: existing emitted literals stay valid and `==`-equal to a fresh
  parse, so `testIRDrift` keeps passing and the 238-file regeneration becomes hygiene
  rather than a blocker (see §7).
- Parser: concrete syntax, held to reject-never-weaken — which requires §0 first.
- Lowering: `resetOf : vars → n → Side → PMode → Option (List (Fin n × ITerm n))`,
  mirroring `dynOf` (`Trusted/Run.lean:109`).
- The guard convention already matches: guards are indexed by target mode (`hostGuard`
  reads `m.guard`, `CoverInstance.lean:39`; the guard is threaded as `Gd`, consumed as
  `sat (Gd e.tgt) μ`).
- Emission doors: `--emit-ir` round-trips resets; two new probe kinds per mode
  (reset-preserves-invariant, reset-lands-in-domain, §3.4).

### 3.2 Checker data

- The reset rides the **target mode**, matching `ρ_m`. `decideCovered` unchanged.
- The obligation lives in the **certificate** (`CoverCert`/`CoverCertMC`), not the
  decision procedure — a `resetPres` field alongside the existing static
  `repoPresPre`/`repoPresPost`.
- `Checker/Cover.lean` is upstream of the whole proof layer ⟹ one world rebuild,
  batched (§7).

### 3.3 The proof layer — where the work is

**Loop shape.** The model of interest is *jump-then-flow*; `modeStep` is
*flow-then-jump*. A rotation, scoped separately in `docs/ROTATION-SCOPE.md`.

**The load-bearing assumption to break.** `RightReachG.jump`
(`Proofs/Soundness/CutCover.lean:136`) hands the *same* `μ` to its continuation — that
is "state is continuous at a switch", stated once and consumed everywhere. It becomes
`… → μ' = applyReset … μ → RightReachG … μ' ω`, and this hits **five constructors**:
`jump` plus all four `reposition*` — every reposition also traverses a declared edge.
The reposition bridges were tightened *against* state preservation
(`Cover.lean:250-253`), so a reset changes the contract they satisfy.

**The preservation induction.** `pres` / `pres_multi_cut` (`CutCover.lean:274`) closes
each jump case at the *same* state, re-entering right cut atoms from the guard. Three
new obligations:
- *invariant across the reset* — a new certificate field backed by a new Z3 query;
- *right cut atoms re-established post-reset* — today's baton re-enters them at the
  switch using the guard; now they must hold at `μ'`. If a reset moves the state out of
  the cut region the cut channel breaks, and that channel is what the 13 cut-reliant
  benchmarks depend on;
- *left cut atoms survive a right reset* — true by variable disjointness, but needs an
  explicit coincidence lemma.

**Encoding side (the harder half).** `modeStep` gains assignments between the guard test
and `mv := e.tgt`; then re-prove `modeStep_sem` (`JointBridge.lean:96`),
`rightReach_is_R_real_run` (`:115`), the cadenced mirrors (`ClockedTop.lean:99,180`), the
multiflow chain data (`RepositionDischarge.lean:359`, `EnvelopeChain.lean:89`,
`UniformMultiflow.lean:104`), and every `Disjoint`/`fv` hypothesis
(`UniformFvDischarge.lean`, `FvDischarge.lean`) — the program's variable set grows.

**Freshness.** `MVFresh` (`JointBridge.lean:52`) and the clock conditions must extend:
reset targets are state variables and must be disjoint from `mv` and `tg`. This is the
family that produced the archived `MvFrozen` vacuity finding
(`Archive/ProbeMvHd.lean` — a disjointness hypothesis provably *false*). Re-run that
check deliberately.

### 3.4 Emission — the obligation is static

No Lie derivative, no ODE:

```
UNSAT(  guardL ∧ guardR ∧ evolveL ∧ evolveR
     ∧  g ≤ 0                                  -- invariant before the jump
     ∧  g[L ↦ ρ_L , R ↦ ρ_R] > 0 )             -- but not after
```

Needs `ITerm.subst` plus a bridge lemma `isubst_toHost`, mirroring `itderiv_toHost` /
`ilieDeriv_toHost` / `iflowQuery_toHost` (`Trusted/Smt.lean:83,98,107`). Printer
unchanged.

### 3.5 Existence and viability

`HExistSegB` (`Proofs/Flow/WellFormedFlow.lean:89`) starts the right flow at the left
segment's endpoint. After a reset it restarts at the **reset image**. Two consequences:

- *landing is a precondition, not a nicety*: the flow runs with domain `evolC_m`
  immediately after the reset, so if `ρ_m(x)` violates it the loop body is stuck and the
  ∃-witness dies outright;
- *re-anchoring is universal*: because the reset sits immediately before the flow,
  **every** mode residence begins at a reset image, so the bounded-viability chain is
  re-entered at a point the model author chose rather than one the dynamics produced.
  This lands squarely on S3's tangential case (an anchor *on* a face, zero budget).
  Contract fields (route a) are unaffected; polynomial fields (route b) pay on every
  entry.

### 3.6 Instances, verdicts, fidelity

New query shape ⟹ new pins in `Verdicts/GenericPins.lean` plus mirrors. `Faithful`
(`Checker/Faithful.lean:357`) already compares per-**mode** data and `ρ_m` is per-mode,
so the fidelity predicate extends along its existing grain — one new clause, still
mandatory (without it the kernel identity would not cover the reset data).

---

## 4. The genuinely hard problems

1. **The cut baton across resets.** The 13 cut-reliant benchmarks certify only because
   guard-derived atoms persist and re-enter at switches. A reset can invalidate an atom
   instantly. Either each reset is shown to preserve each atom (a per-mode, per-atom
   query — the largest new query family), or the cut lift degrades on reset-carrying
   modes. Unknown until tried.

2. **Existence re-anchoring at the reset image** (§3.5) — universal, not occasional.

3. **Repositions get strictly harder, with no compensating gain.** The guard is tested
   *before* the reset, so a reset can never enable a disabled transition. What actually
   happens is the reverse: every hop through `m` drags the right state through `ρ_m`, so
   a multi-hop chain composes resets — `ρ_{m₃}(ρ_{m₂}(ρ_{m₁}(x)))` — and the invariant
   must survive each. Long chains can drift out of the band. In the shelved fixpoint
   design this makes `Serve`'s hop moves costly rather than free.

4. **Repeated self-resets on the left.** Every mode declares itself a successor
   (watertank's `Low` has `next = [Mid, Low]`), so under jump-then-flow a stay may be
   many iterations, each re-applying `ρ_m`. Harmless on the right (we choose the
   witness); on the ∀-quantified **left** the proof must tolerate arbitrarily many
   repeated self-resets in one window. If `ρ` is not idempotent this is a real
   obligation, and easy to miss.

5. **Simultaneity.** A per-coordinate reset map is *simultaneous*; sequential
   `Program.assign`s are not (`x1:=x2; x2:=x1` is wrong). Restrict to **triangular**
   resets (no read-after-write), checked syntactically at parse time — this covers every
   reset seen in practice. Avoid routing through `Side.Aux` scratch coordinates: only
   `n` slots exist and `mv`/`tg` already take two.

6. **One invariant per graph.** `CoverCert` carries a single `g` for the whole graph
   (`Cover.lean:155`), so the obligation is forced into `g(ρ(x)) ≤ 0` for the *same* `g`.
   A reset needing a different invariant across the jump is not expressible without a
   further refactor.

---

## 5. Mandatory soundness gates

- **Cross-side resets must be rejected.** `R_x := L_x` reads the other system's state and
  breaks the `Disjoint varsL varsR` premise the entire relational encoding rests on. The
  parser must reject it, mirroring the existing side discipline (`namesFree "L_"`,
  `lowerE_fv_side`). Highest-risk item: easy to write, looks natural, silently
  invalidates the encoding.
- **Reset targets must be own-side state variables** — never `mv`, never `tg`.
- **Triangularity** (§4.5), checked at parse time.
- **Fidelity must cover resets** (§3.6).
- **Identity default reduces definitionally**, so the 46 existing benchmarks keep
  literally the same proofs.

---

## 6. Scope tiers

| tier | admits | difficulty |
|---|---|---|
| **T1 — deterministic, same-side, right-only** | `R_x := ρ_m(R_x)`, polynomial, triangular, on R's modes | the tractable core |
| **T2 — both sides** | L's windows also reset | **not symmetric with T1.** The top theorems take the left as a flat `star (bigChoice leftProgs)` (`BridgeFinish.lean:78-90`, `EnvelopeChain.lean:389`, `RepositionEndToEnd.lean:46`) with left guards and edges discarded. A left reset requires building the left analogue of the whole `mv`/`modeStep`/`R_real` apparatus — the GAP 1–3 arc — in a setting where one such freshness hypothesis was already mechanized as *unsatisfiable* (`ProbeMvHd.probe_hd_false`). Plus the ∀-side self-reset obligation (§4.4). **Exclude from v1 and say so.** |
| **T3 — nondeterministic / guarded resets** | `x := *` with a post-condition | `Program.assignAny` exists, but the ∃-witness must now *choose*, and the cover certificate becomes a choice structure — a different, larger design. Out of scope. |

---

## 7. Effort and rebuild

| layer | effort |
|---|---|
| DSL + parser (incl. §0 prerequisite) | S–M |
| model IR (`PMode.reset` defaulted, cover plumbing) | S–M |
| **kernel chain (obligation, `RightReach`, `pres`, encoding lemmas, fv re-discharge)** | **L — dominant** |
| emission (`ITerm.subst`, `isubst_toHost`, `resetUnsat`, `--emit-*`) | M |
| printer / `Faithful` (new clause, `hostReset_pin`) | M (S for drift if the field is defaulted) |
| tests + a reset-carrying benchmark (full generated column, `suite_audit.py` exemption) | S–M |

**Regeneration inventory** if `PMode` gains a field: `Instances/BenchIR/*` (46) ·
`FaithfulCerts` `rfl` (46) · `BenchCovers` (46) · `BenchCoversNC` (33) ·
`EvolStrengthenings` (46) · `Throughout` (33) · `CutThroughout` (13) = **238 generated
files**. But a **Lean default on the new field keeps existing literals valid and
`==`-equal to a fresh parse**, so `testIRDrift` keeps passing and regeneration is
hygiene, not a blocker. The kernel-chain edits still force one world rebuild (the proof
layer is upstream of everything); batch everything into it.

**Cheapest decision-complete probe** (≈ a day, no rebuild): hand-write one
reset-carrying benchmark, run the *existing* tool on the pre-reset and post-reset models
as two separate problems, and check by hand whether (a) the invariant survives the
substitution, (b) the reset image lands strictly inside the target domain, (c) the cut
atoms survive. That settles hard problems 1 and 2 before any Lean work starts.

---

## 8. Bottom line

Structurally favourable: the object language, the top-level statement, the decision
procedure, and the printer all survive untouched, so the trust base does not grow. The
work concentrates in one place — the transition relation hard-wires "state is continuous
at a switch" across five constructors, and unpicking that ripples through the
preservation induction, the witness extraction, the encoding lemmas, and the existence
anchoring.

Not hard in the sense of "we do not know how"; sized in the sense of "an S2-shaped arc
plus one world rebuild", with two empirical unknowns a one-day probe would settle, and
one prerequisite (§0) worth doing regardless.

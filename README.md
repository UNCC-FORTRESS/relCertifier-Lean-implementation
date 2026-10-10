# relCertifier-lean

A **fully mechanized relational certifier** for hybrid-system refinement, in Lean 4.

Given two hybrid automata — an ideal system `L` and an implementation `R`, written in a
small textual DSL — it certifies relational invariants of their co-execution
(`|L_x − R_x| ≤ ε`-style bounds) and delivers, per benchmark, a **kernel-checked
end-to-end theorem** whose only assumptions are a five-item trust base and a finite list
of Z3 `unsat` verdicts, each re-runnable on demand.

Everything is Lean: the parser, the lowering, the query printer, the search, the
certificate checker, the proofs, and the per-benchmark theorem instances. Z3 is the
single external oracle, consulted only through printed SMT scripts, and only its
`unsat` answers are trusted.

**Status.** All 34 certified benchmarks carry the modal (Theorem 3) statement — 35 base
theorems, since one benchmark splits per left mode — and, beside them, 7 mode-keyed and
2 cut-composed theorems at the DECLARED invariants, plus the pruning-suite theorem of
`match_multi_rate` over its enlarged automaton and the Theorem 2 instance of its pruned
edge (46 theorems in `ModalBattery`): 36 audit to the three standard Lean axioms plus
`z3_unsat_sound`, 10 to the three standard axioms alone (measured 2026-10-09). On 2026-10-09 the certifier's static
(zero-duration) reposition was removed (`docs/COVER-AUDIT.md`); six benchmarks that needed
it (`arm_chain_rung1`, `arm_chain_rung2`, `arm_fidelity_low`, `robot_braking`,
`rover3tier_M1`, `watertank`) are now DECLINED and left the battery (40 → 34 certified,
52 → 46 theorems). No `sorry`, no `admit`, no
`native_decide`. The last cold-tree verification (2026-08-02, 12h59m, 8988 jobs, exit 0)
predates the 2026-10-08 suite deduplication and covered the 46-benchmark suite of that
time; every check has been re-run warm on the 40-benchmark suite since (`STATUS.md`).

**Non-connection pruning exercised (2026-10-08).** The paper's Section 4.3 device — a
declared right edge pruned from the cover's all-successors obligation on two Z3 `unsat`
verdicts — was implemented but fired on no benchmark. `match_multi_rate` now declares
(additively) a stall fallback `STALL` with the edge `DRIVE → STALL`; the certifier prunes
it, `RELCERT_NO_PRUNE=1` makes the benchmark DECLINE, and the pruned edge's two queries
are a fifth `--run-verdicts` phase with declared counts, pinned to the kernel-stated
Theorem 2 instance. Thirteen other candidates were tried by runs and dropped: under the
paper's definition their emergency mode is an *admissible initial* right mode, which the
cover must cover whether or not the edge into it is pruned. The lowering accepts
right-only variables, so `shield_unreachable` runs (DECLINED, with and without pruning:
its `Shield` guard is a closed compound band). [`docs/PRUNING.md`](docs/PRUNING.md).

**Suite deduplication (2026-10-08).** Six benchmark directories were byte-identical
copies of others once comments, blank lines and the `name =` line are stripped
(`arm_fidelity_high` = `plant_fan_high` = `arm_chain_rung3`; `arm_refinement` =
`plant_fan_low` = `arm_fidelity_low`; `match_multi_eps` = `rover3tier_M1`), and
`plant_fan_mid` differed from `arm_fidelity_mid` only in its tolerance constant. The six
were removed, with every instance, pin, runner row and coverage constant that named them;
the certified suite is 40 benchmarks (41 inputs with `shield_unreachable`). Method, the
removal list and the per-benchmark theorem table: [`docs/SUITE-DEDUPE.md`](docs/SUITE-DEDUPE.md).

**Mode-dependent invariants (2026-10-07).** Seven benchmarks declare one invariant row per
left mode. The tool checks the cross-mode **handoff** `φ_inv(m') ∧ evolve_{m'} ∧ guard_m ∧
evolve_R → φ_inv(m)` at every declared left transition (`relcert --handoff`; phase 4 of
`--run-verdicts`), and `Proofs/Encoding/ModeHandoff.lean` composes per-left-mode theorems
with those handoffs into the paper's general Theorem 3 at the mode-keyed invariant
`⋀_m (u_L = m → φ_inv(m))` over the full left automaton. All seven carry that composed
theorem (`…_modeKeyed`); `rover3tier_rung12`'s ACCEL row had to be re-stated first (rows
only; its original row failed the handoff, countermodel recorded).
[`docs/HANDOFF.md`](docs/HANDOFF.md), [`docs/PAPER-MAPPING.md`](docs/PAPER-MAPPING.md) §2b.

**Every verdict hypothesis has been checked true.** A kernel-checked axiom list says a
proof did not cheat; it cannot say the theorem's *hypotheses* hold, and a theorem with a
false hypothesis is vacuously true. An audit of all 42 `Verd` definitions on 2026-07-31
found six that were vacuous, and all six were repaired the same day
([`docs/VERDICT-EVIDENCE-AUDIT.md`](docs/VERDICT-EVIDENCE-AUDIT.md)). Five of those
repairs add a **region conjunct** to the invariant — see *Conditioning* below.

### Contents

1. [Quickstart](#quickstart)
2. [The end-to-end guarantee, intuitively](#the-end-to-end-guarantee-intuitively)
3. [How one benchmark becomes a theorem](#how-one-benchmark-becomes-a-theorem) — the pipeline, step by step
4. [Well-formedness: why the hypotheses exist and how they are discharged](#well-formedness)
5. [suite_v2 — the paper's suite, all 45 with Theorem 3](#suite_v2--the-papers-suite-all-45-benchmarks-with-theorem-3-2026-10-10)
6. [Theorem families and status](#theorem-families-and-status)
7. [Repository map](#repository-map)
8. [File guide — what each file is *for*](#file-guide)
9. [Lean mechanization ↔ the paper](#lean-mechanization--the-papers-formal-results)
10. [Re-checking the guarantees](#re-checking-the-guarantees)
11. [Soundness findings](#soundness-findings)
12. [Benchmarks and further reading](#benchmarks)

---

## Quickstart

```bash
lake build                                   # whole development (proofs + instances)
lake build relcert                           # the certifier executable
./.lake/build/bin/relcert --help             # all commands, and what is NOT in this binary
./.lake/build/bin/relcert benchmarks/suite_uniform/watertank/input.txt   # certify one
./.lake/build/bin/relcert --run-verdicts     # empirically re-check theorem hypotheses

# the two fast checks in one command (certify the suite, then discharge hypotheses):
./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt
```

**Which command checks what.** The kernel check and the tool check are deliberately
separate, and they live in different places:

| what you want to check | command |
|---|---|
| the Lean proofs (kernel) | `lake build` — everything, ~13 h |
| the 46 theorems + their axioms | `lake build RelCertifier.Instances.ModalBattery` |
| the benchmarks certify (the tool) | `relcert <input.txt>...` |
| the theorems' Z3 hypotheses hold (+ the cross-mode handoff, + the pruning queries) | `relcert --run-verdicts` |
| the same with pruning switched off (the Section 4.3 ablation) | `RELCERT_NO_PRUNE=1 relcert <input.txt>...` |
| the handoff alone, per benchmark | `relcert --handoff <input.txt>...` |
| both of the fast ones at once | `relcert --check-quick <input.txt>...` |
| parser / printer / IR-drift / determinism | `BENCH_PATHS=<manifest> relcert-test` |

`--check-quick` compares the certification tally against the suite declared in
`Verdicts/Coverage.expectedSuite` (34 certified, 7 declined — the documented
`shield_unreachable` and the six declined after the static-reposition removal — 0 errors), so a benchmark that starts failing cannot hide among
the expected results. Give it a different path set and the tally is reported but not enforced.

A full `lake build` is **~13 hours** (12h59m measured from cold, 2026-08-02) and peaks
near 30 GB; see the *Cost* section of
[`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md) before starting one. To
check a single file against already-built dependencies, use `lake env lean <file>`
instead — one process, reusing existing oleans.

Current state in one page — what is proved, assumed, and open: [`STATUS.md`](STATUS.md).

Reports land in `docs/VERDICTS.md`. Axiom audits: see [Trust audit](#trust-audit).
**Reproducing the whole certification claim, step by step:**
[`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md).

---

## The end-to-end guarantee, intuitively

**What is being proven.** The paper's Theorem 3 shape: *whatever the ideal system `L`
does, the implementation `R` can respond so that the relational invariant holds — and
keeps holding through every round.* "Whatever `L` does" is a `∀` over `L`'s runs
(windows of its modes, clock-capped); "`R` can respond" is an `∃` over `R`'s runs
(certified flow pieces, possibly opened by *repositioning* `R` through its declared mode
graph when its current mode carries no certificate for the window). The loop invariant
that survives the rounds is the relational invariant strengthened with the mode-validity
and envelope bookkeeping the response construction needs.

In Lean the statement is literally

```lean
RFormula.rvalid (theorem3Form  (bigChoice leftProgs)          -- L: the window family
                               (rightAutomatonBody Gr mv)     -- R: the mode automaton
                               (canonInvM g gs ∧ envLR domL domR ∧ mvValidR mv k))
```

where `theorem3Form L R ϕ = ϕ → [|(L*, R*)⟩⟩ ϕ` — the invariant implies that it survives
the ∀∃ modality over both starred programs.

**Three ingredient kinds, three trust levels.**

1. **Proved once, for all benchmarks** (pure Lean, three axioms): the ∀∃ proof calculus —
   how per-piece flow certificates compose into window responses, how reposition hops
   re-anchor, how the loop closes (`Proofs/Encoding/`). Also the analytic facts:
   differential-invariant rules, Picard existence, bounded-time viability, explicit
   exponential witnesses for contract fields (`Proofs/Flow/`).

2. **Checked per benchmark by the kernel** (still three axioms): that the instance data
   *is* the benchmark — the emitted IR is what the parser produced (drift-checked
   literals), the cover decision replays (`decide`), the lowered queries in the theorem
   are identical to what the runner prints (the *pins*, `Verdicts/`), well-formedness of
   the cut certificates, side-splits, encodings.

3. **Observed** (the fourth axiom, `z3_unsat_sound`): a finite list of named facts
   `z3solve (query) = unsat`. `z3solve` is an *opaque* constant — operationally, the
   printer plus a Z3 process. Running `relcert --run-verdicts` is what discharges these.
   The kernel pins (ingredient 2) guarantee the printed query is exactly the one the
   theorem names, so nothing can drift in between.

**The trust boundary, exactly.** A benchmark's theorem holds if you accept:

| assumption | why it is irreducible |
|---|---|
| the **parser** reads the benchmark file correctly | the file is the spec |
| the **printer** (`toScript`) renders formulas to SMT faithfully | Z3 reads text |
| **Z3's `unsat`** answers are correct | the one oracle (axiom `z3_unsat_sound`) |
| the **Lean kernel** | checks everything else |
| **successor-completeness with guard-gated switching**: every mode change of `R` enters a *declared* successor, and at that instant the entering mode's guard holds. The certificate relies on it only at the two kinds of switch it uses: the end of a **joint segment** (both systems flowed) and the end of a **dynamic reposition** (`R` flowed alone, under its own field, for a full interval while `L` is held — the paper's right-only segment). The certificate makes **no zero-duration switch**: the static reposition, which moved `R` into a successor at a single instant, was removed on 2026-10-09 (`docs/COVER-AUDIT.md`) | the automaton's transition semantics — a fact about the modeled system, not about formulas |

Nothing else. In particular the search — cover exploration, cut fixpoints, route
selection, λ choice — is **completely untrusted**. It only *proposes*; every accepted
output is re-validated by kernel-checked replay or becomes a named Z3 fact.

**Conditioning (the two region-carrying instances).** `arm_chain_rung3` and
`arm_fidelity_mid` (five instances before the 2026-10-08 deduplication) state their base
invariant as `θ_R ≥ 0.6 ∧ (the benchmark's relational invariant)`. The extra conjunct is
exactly the `Hold` mode's guard, and it is *necessary*: the tool certifies `Hold` at that
narrowed domain (the emitted cover records `jointOK = true` there), and without it the
flow query is satisfiable, so the theorem would be vacuous. These two therefore claim:
*from states where the right system already satisfies `Hold`'s guard, the refinement is
maintained.* That is what the certificate supports, stated honestly. The same device
(`lowFace`, a region as an invariant component) is what `rung2c` has always used.

**Cut composition (2026-10-08).** Each of the two also carries a second theorem,
`<name>_declared` (`Instances/<Name>Declared.lean`), at the DECLARED invariant with the
cut carried only where the tool checked it — as `Hold`'s mode region (`mvRegionR`, `⊤` at
the approach modes). From every state satisfying the declared invariant with the right in
an approach mode, and from every state in `Hold` inside its guard, the refinement is
maintained; the response is a Z3-free right-only catch-up (standard three axioms). The
declared invariant with no region anywhere is false for these automata (from `Hold`
below its guard the right cannot move): `docs/CUT-COMPOSITION.md`,
`docs/PAPER-MAPPING.md` §2c.

**Coverage.** The modal statement is instantiated for all 34 certified benchmarks;
`Instances/ModalBattery.lean` imports every one and re-emits its axiom audit on each
build. Five are entirely **Z3-free** (`rover3_M1`, `rover_coupled`, `rover_position`,
`refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof`): their
responses are pure right-side flows with the invariant re-established by endpoint
arithmetic, so no flow certificate — and no verdict hypothesis — appears at all.

---

## How one benchmark becomes a theorem

This is the pipeline every benchmark travels, with the file responsible for each step.
Steps marked **TRUSTED** are inside the trust base; every other step is either
kernel-checked or untrusted-and-then-re-checked.

```
benchmarks/suite_uniform/<name>/input.txt            ①  the spec, as text
   │  Trusted/Parse.lean + Trusted/KeyAudit.lean     ②  parse            ← TRUSTED
   ▼
Parse.PProblem                                       ③  the IR value
   │  Trusted/EmitIR.lean  (--emit-ir)
   ▼
Instances/BenchIR/<name>.lean   `<name>_IR`          ④  the frozen literal
   │  ▲ relcert-test [ir-drift]: re-parse and compare
   │  ▲ Instances/FaithfulCerts.lean: kernel `rfl` certificates
   │
   │  Trusted/Run.lean                               ⑤  lower to host terms
   ▼
Term (Var n) / Formula (Var n),  Var n = Side × Fin n
   │  Trusted/OracleAPI.lean                         ⑥  SEARCH           ← UNTRUSTED
   ▼
a proposed cover: λ, windows, routes, cuts, repositions
   │  Checker/CoverEmit.lean  (--emit-cover)
   ▼
Instances/BenchCovers/<name>.lean                    ⑦  the certificate
   │  Checker/Cover.lean `decideCovered`, replayed by `decide`
   │  Checker/Checker.lean `decideCovered_sound`     ⑧  KERNEL REPLAY
   ▼
`Covered …`  — a proof-grade fact
   │  Proofs/Encoding/*  (the ∀∃ calculus)           ⑨  compose
   ▼
Instances/<Bench>Modal.lean                          ⑩  the instance
   │  #print axioms                                  ⑪  audit
   ▼
rvalid (theorem3Form …)   +   a finite list of `Verd…` Z3 hypotheses
                              discharged by --run-verdicts, pinned by Verdicts/
```

### Worked example: `watertank`

*Historical (2026-10-09).* This walkthrough describes the `suite_uniform/watertank`
instance as it stood before the static (zero-duration) reposition was removed. That
benchmark's cover needed the static reposition, so it is now DECLINED, and its Lean files
(`Instances/WatertankModal.lean`, `WatertankViability.lean`, `Verdicts/Watertank.lean`)
were deleted; they remain in the git history (commit `3494c49`). The pipeline stages
described here are unchanged for every certified benchmark. The paper's running example
is now the redesigned `benchmarks/suite_v2/watertank` (set-point pumps, sensor offset 3,
tampered Low pump), which certifies with joint segments only.

**① The spec.** A tank whose controller is attacked two ways — a sensor offset of −3 and
a fill speedup in the Low mode. Each mode is a proportional controller, so each ODE is a
first-order relaxation toward a setpoint:

```ini
[Lsys.mode.Low]
ode    = x' = smt2:(* 3 (- 0.6 (* x 0.04)));      # deployed: setpoint 15
guard  = x >= 0.0 and x < 13.0                    # shifted by the sensor offset
evolve = x >= 0.0 and x <= 25.0
next   = [Mid, Low]

[Rsys.mode.Low]
ode    = x' = smt2:(* 3 (- 0.5 (* x 0.04)));      # nominal: setpoint 12.5
guard  = x >= 0.0 and x < 10.0
evolve = x >= 0.0 and x <= 25.0
next   = [High, Low]

[relational_invariant]
Low  = x[l] <= x[r] + 3
Mid  = x[l] <= x[r] + 3
High = x[l] <= x[r] + 3
```

The question the certifier answers: *can the deployed tank always stay within 3 of the
nominal one, no matter how the deployed one behaves?*

**② Parse — TRUSTED.** `Trusted/Parse.lean` is strict: it rejects rather than repairs.
`Trusted/KeyAudit.lean` gates every CLI parse site so an unknown key is an error rather
than a silent drop — writing `reset = x2 := 1` into a mode section now fails with exit 1
instead of being discarded (see `docs/proposals/RESET-MAPS-SCOPE.md` §0).

**④ Freeze the IR.** The parse result is emitted as a Lean literal, `watertank_IR`. Every
downstream instance *quotes that literal* — no model data is ever re-typed by hand into a
proof. Two independent checks keep it honest: `relcert-test` re-parses the input file and
compares, and `Instances/FaithfulCerts.lean` carries kernel `rfl` certificates tying the
literal to the transcribed instance data.

**⑤ Lower.** Model variables become `Var n = Side × Fin n`: `Lv i` for the left system,
`Rv i` for the right, plus a disjoint aux range for bookkeeping (the mode counter `mv`,
the clock `tg`). This split is what makes a *relational* formula encodable as an ordinary
host formula.

**⑥ Search — UNTRUSTED.** The tool explores mode covers, picks the time-stretch λ, and
selects a differential-invariant route per (window, mode) pair. Nothing here is believed.

**⑦–⑧ Emit and replay.** The chosen cover is emitted as data, then `decideCovered` is
*recomputed by the kernel* via `decide`, and `decideCovered_sound` converts a `true`
replay into a `Covered` fact. If the search had lied, the replay would fail.

**⑨–⑩ Compose and instantiate.** `Instances/WatertankModal.lean` builds the left window
family and right mode graph, discharges the side conditions (see
[well-formedness](#well-formedness)), and applies the generic top theorem from
`Proofs/Encoding/EnvelopeChain.lean`. `WatertankViability.lean` then discharges existence
*outright* using the explicit exponential witness for contract-shaped fields, so no
existence hypothesis survives.

**⑪ What remains.** `watertank_modal_certified` has exactly six hypotheses — route
verdicts, all observed `unsat` — each tied to the runner's printed query by a kernel
identity theorem in `Verdicts/Watertank.lean`. Under the trust table above, that theorem
holds, full stop.

### What differs across benchmarks

The pipeline is identical; three knobs vary.

* **Invariant arity.** Single-component invariants use `EnvelopeChain.lean`; the 19
  multi-component ones (up to 8 conjuncts) use `EnvelopeChainM.lean`, which runs the same
  chain over a *list* of components.
* **How existence is obtained.** Contract-shaped fields get explicit witnesses; most get
  viability certificates (strict faces, or growth faces with entry budgets); the five
  catch-up instances need none, because their responses are closed-form flows.
* **How the response is built.** Most benchmarks respond in place or hop statically along
  declared edges. Three switch mode *inside* a window (`SplitCoupling.lean`, capped at
  `dt ≤ 1/5`). Five respond with pure right-side flow and close the invariant by endpoint
  arithmetic (`WindowGrowth.lean`). One states two theorems, one per left mode.

---

<a name="well-formedness"></a>
## Well-formedness: why the hypotheses exist and how they are discharged

"Well-formedness" covers five genuinely different obligations in this development. They
are worth separating, because they are discharged by different means and sit on different
sides of the trust boundary.

### 1. Syntactic — the ODE system is a function, not a relation

`ODESystem.WellFormed sys` is `(sys.map Prod.fst).Nodup` (dL-lean, `Syntax.lean`).

**Why it is needed.** An ODE system here is a *list* of `(variable, term)` pairs. Nothing
in the datatype stops a variable from appearing twice — and if `x` had two assigned
derivatives, "the field at `x`" would be ambiguous and `odeField` ill-defined. dL-lean
deliberately keeps the datatype loose and states the constraint separately, mirroring
Isabelle's `osafe` and Coq-dL's `wf_ode`.

**How it is discharged.** Structurally, in the kernel. `leftBlock`/`rightBlock` are built
by mapping `List.finRange n` through the injections `Lv`/`Rv`, so nodup follows from
`(List.nodup_finRange n).map`. For clocked systems the clock variable is appended, and
`clk_wellFormed` (`Proofs/Encoding/WindowGrowth.lean`) discharges the extended system
given `tg ∉ sys.bound`. **No solver, no axiom.**

### 2. Freshness — the bookkeeping variables must not collide with the model

Obligations of the shape `mv ∉ g.fv`, `tg ∉ domR.fv`, `Disjoint (…).varsL (ρ '' (…).varsR)`.

**Why it is needed.** The encoding introduces variables the modeled system does not have:
`mv` records which mode `R` is in, `tg` is the window clock. If either collided with a
model coordinate, the bookkeeping would silently corrupt the dynamics. The L/R disjointness
is stronger still: it is the *precondition of the encoding itself* — a relational formula
becomes an ordinary host formula only because left and right variables occupy disjoint
ranges (`rvalid_of_encoded_unsat` takes it as a hypothesis).

**How it is discharged.** By side-split lemmas that trace every lowered object's free
variables back through the lowering pipeline to `range Lv` or `range Rv`, with the aux
variables in a third range: `FvDischarge.lean`, `UniformFvDischarge.lean`,
`LoweringSide.lean`. In instances these appear as small `simp`/`decide` proofs.
**Kernel-checked, no solver.**

### 3. Semantic — the response flow actually exists and stays in its domain

This is the substantive one. `WellFormedFlow fR lam domR` says: from **every** in-domain
start and for **every** duration `s ≥ 0`, the right block's ODE has a solution that starts
there, freezes the non-right coordinates, and **stays in `domR` throughout**.

**Why it is needed.** The `∃` side of Theorem 3 must exhibit a real run of `R`. A run of
`{x' = f & dom}` requires both that the ODE has a solution (Picard) *and* that the solution
never leaves `dom` — otherwise the program simply cannot take that duration, and the
response does not exist.

**The honest finding: the `∀s` form is false.** This is mechanized, not hand-waved.
`WellFormedFlow_rover_false` (`Archive/RoverLandingInstance.lean`) proves
`¬ WellFormedFlow roverFR roverLam recoverDomVx`: the rover's Recover mode has
`vx' = 0.4` constant under domain `vx ≤ 1`, so at `s = 3` the forced value is
`0 + 0.4·3 = 1.2`, outside the domain. No witness can exist. Domain-invariance is
**duration-bounded**, not free.

So the development uses `WellFormedFlowB fR lam domR dt` — the same statement with
domain-staying required only for `s ≤ dt`, where `dt = ε_r/λ` is the cover's segment
budget. That is exactly what the tool checks per segment, and it is true for these fields
over one short segment. `WellFormedFlowB_of_WellFormedFlow` records that the bounded form
is strictly weaker.

**How it is discharged**, three ways depending on the benchmark:

| route | mechanism | benchmarks |
|---|---|---|
| **proven outright** | explicit exponential witness for contract-shaped fields (`contractΦ`, `Proofs/Soundness/UniformEvol.lean`) | watertank and the contract family |
| **from viability certificates** | strict faces by a first-exit argument (`BoxViability.lean`); growth faces with entry budgets, telescoped (`BoxViabilityBounded.lean`); assembled in strata by `StratifiedFaces.lean`, with equilibrium and monotone faces in `AffineFaces{,2}.lean`. Suite-wide census: 1085/1085 evolve-box faces (`BenchViability2.lean`; 1121 before the deduplication) | most of the suite |
| **not needed at all** | the response is a closed-form flow written down directly (linear, or the exponential `v(t) = c + (v₀−c)e^{−3t}`), so existence is a witness rather than a hypothesis | the five Z3-free catch-up instances |

The middle route bottoms out at face verdicts, i.e. at `z3_unsat_sound` — no *new* trust,
the same single oracle. The first and third routes involve no solver at all.

### 4. Bundled side conditions — `LandingWellFormed`

`Proofs/Flow/MultisegLanding.lean` bundles, per benchmark: `0 ≤ dt`, the landing
hypothesis, `mv`/`tg` freshness, that every graph mode really has the right-block shape,
`WellFormedFlowB`, a `BoxLe` invariant-preservation fact, and the existence of a self-edge
and of retained-successor edges with `⊤` guards.

**Why bundle.** The loop needs all of these *simultaneously, at every mode*, on each
round. Bundling turns a scattered pile of per-mode obligations into one structure an
instance discharges once; `hHcouple_of_LandingWellFormed` then derives the dispatch.

### 5. Decidable model well-formedness — the settling family

`Checker/WellFormedChecker.lean` defines `decideWellFormed : SettlingModel n → Bool`,
checking band ordering and per-mode coordinate shapes (`frozen`, `constRate`, `contract`,
`riccati`) with their parameter side-conditions — for instance, that a quadratic-drag
mode's equilibrium `√(10⁶b/a)` lies inside the band. Its docstring is the summary:
*"Decidable; no Z3, no ODE reasoning."* Variants exist for terrain and affine models.
Instances discharge it by `decide`; `WellFormedSound` converts the `true` into the
semantic fact.

### Summary — which side of the boundary each obligation sits on

| obligation | how discharged | trusted? |
|---|---|---|
| `ODESystem.WellFormed` (nodup) | kernel, structural (`nodup_finRange.map`) | **mechanized** |
| freshness / L-R disjointness | kernel, side-split lemmas | **mechanized** |
| `WellFormedFlowB` — contract fields | kernel, explicit exponential witness | **mechanized** |
| `WellFormedFlowB` — general | viability chain, bottoming at face verdicts | **mechanized** modulo the Z3 leaf |
| `WellFormedFlowB` — catch-up instances | closed-form witness | **mechanized** |
| `LandingWellFormed` bundle | kernel, per-instance discharge | **mechanized** |
| `decideWellFormed` (settling models) | kernel `decide` + `WellFormedSound` | **mechanized** |
| successor-completeness, guard-gated switching (at the end of joint segments and full-interval dynamic repositions only; no zero-duration switch is made) | **not discharged** | **TRUSTED** — a modeling fact about the automaton, not a fact about formulas |

The last row is the only well-formedness-flavoured item inside the trust base, and it is
there for a principled reason: it says the *modeled system* only ever switches into
declared successors whose guards hold. That is a statement about what the automaton is,
which no amount of formula manipulation can establish.

---

## suite_v2 — the paper's suite, all 45 benchmarks with Theorem 3 (2026-10-10)

`benchmarks/suite_v2/` (45 benchmarks; `benchmarks/README.md`) is the suite the paper
reports. **Every one of the 45 carries a kernel-checked Theorem 3**, re-emitted with its axiom
list on every build of `RelCertifier/InstancesV2/BatteryV2.lean`:

| theorem family | count | which |
|---|---|---|
| total (one Theorem 3 per benchmark) | **45** | 26 new instances in `InstancesV2/Modal/`; 19 benchmarks copied unchanged from `suite_uniform` reuse their legacy theorem (`InstancesV2/SameIR.lean`: the v2 IR literal IS the legacy literal, `rfl`) |
| mode-keyed (declared per-left-mode rows, composed by `ModeHandoff.theorem3_modeKeyed`, handoffs in-kernel) | **12** | `acc_spoof_limp`, `acc_tune_limp`, `platoon_delay_linkloss`, `platoon3_linkloss`, `rover_patrol_zones`, `rover_patrol_refine`, `sat_detumble_phases`, `sat3w_detumble_phases`, `story3_rollover_ladder_rung_b` (new); `rover3tier_rung12`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof` (copied) |
| X-channel (the widened cut channel `RELCERT_IMPLIED_CUT=1` is needed: closures, implied contractions, linear-form chains; lifted by `Proofs/Soundness/CutLiftX.lean`) | **12** | `acc_spoof_lag`, `arm_plateau_{crit,profiles,slow}`, `charger_fast_setpoints`, `platoon3_{linkloss,profiles}`, `platoon_delay_{linkloss,profiles}`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `watertank` (each DECLINES without the channel) |
| Z3-free (the standard three axioms only, no verdict hypothesis) | **5** | `arm_plateau_{crit,profiles,slow}`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof` |
| on the nonblocking region (a conserved-quantity band of the MODEL in the right region; enters no verdict query) | **6** | the satellite family: `−2 ≤ h + 5 w3 ≤ 2` (one wheel), `−2 ≤ h_i + J_i w_i ≤ 2` per wheel axis (three wheels); `docs/SUITE-REDESIGN.md` §19.2 |

Every hypothesis is a Z3 verdict pack pinned to the query the runner sends
(`VerdictsV2/PinsV2.lean`) or a copied legacy pack (`Verdicts/ModalPinTable`):
`relcert --run-verdicts-v2` discharges 262 modal + 186 handoff + 88 non-connection + 385
copied-benchmark queries, all `unsat`, against counts derived from the tables in-kernel
(`docs/VERDICTS.md`, suite_v2 section). The axiom audit (51 `#print axioms` lines in
`BatteryV2`: 46 benchmark theorems — `match_multi_rate` has its Theorem 2 instance as well —
and 5 generic lemmas): every one is `[propext, Classical.choice, Quot.sound]`, 42 with
`z3_unsat_sound` in addition, 9 without (the 5 Z3-free benchmarks and 4 generic lemmas).
**The trust base is unchanged**: the strict parser, the SMT printer + Z3 (`z3_unsat_sound`),
and the Lean kernel.

Build and check (`docs/CERTIFICATION-CHECK.md`, suite_v2 section):

```bash
lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"
lake build relcert relcert-test
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test      # [ir-drift-v2]: 45 literals
```

Two model findings of the mechanization are recorded in `docs/SUITE-REDESIGN.md` §19: the
track-end odometer wall `s ≤ 100` of `rover_patrol_{zones,refine}` blocked the reference
flow (removed; both still CERTIFIED with unchanged cells), and the satellite wheel-momentum
band blocks right flows, so those six theorems are stated on the nonblocking region.

---

## Theorem families and status

| family | statement shape | benchmarks | where the mode guard lives | hypotheses beyond the trust base |
|---|---|---|---|---|
| **settling** (`*_real`) | cadenced rounds settle into the invariant band (`GuardSettlingB`) | 40/40 | **in the statement**, as `Gd q`. Its final conjunct — *some retained successor's guard holds at the segment's end* — is **non-blocking, proven** | flow/cut verdicts |
| **throughout** | every component of the invariant holds throughout every right coexecution | 23 cut-free | **in the statement**, as `Gd` threaded through `RightReachG` | cover verdicts |
| **cut throughout** | same, via the guard-threaded cut lift | 11 cut-reliant | **in the statement** as `Gd`, *and* as guard-derived cut atoms | cut-narrowed cover verdicts + per-atom O2 probes |
| **modal (Theorem 3)** | `rvalid (theorem3Form …)` — the paper's ∀∃ with reposition-opened windows | **34/34**, 35 base theorems (+ 7 mode-keyed, + 2 cut-composed) | **not in the statement** for most: the R *program* appears instead, with edge guards `⊤`. **Two carry the landing mode's guard as a region conjunct in the invariant** (see *Conditioning*; their `…_declared` theorems carry it as `Hold`'s mode region only) | per-instance route verdicts, **all checked true** (2026-07-31); existence **proven** for every instance. Five base instances need no verdicts at all |

The guard column is the one to read when relating these to a paper's automaton
`( ⋃_m ?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; {x' = f_m & evolC_m} )*`: the first three
families carry the guard *in the statement* and never mention a program, so questions
about program shape or edge guards do not arise for them. Only the modal family puts a
program in the statement.

---

## Repository map

```
RelCertifier/
  Core/       3 files    shared syntax-level machinery below both columns
  Trusted/    10 files   the tool — parser, lowering, printer, Z3 session, search
  Checker/    9 files    certified checking: what replaces trusting the search
  Proofs/                the benchmark-independent calculus (3 axioms)
    Encoding/   35 files   the ∀∃ chain: bridges, windows, repositions, envelopes
    Flow/       14 files   analysis: DI routes, Picard, viability, faces
    Soundness/  6 files    cut lift, guard threading, contract witnesses
    Transfer/   5 files    rescaling and faithfulness bridges
  Instances/  54 files   KERNEL COLUMN: per-benchmark theorems + emitted data
    BenchIR/        40     drift-checked IR literals, one leaf per benchmark
    BenchCovers/    40     emitted cover data (+ BenchCoversNC/ without cuts)
    Throughout/     29     cut-free throughout instances (generated)
    CutThroughout/  11     cut-lifted throughout instances (generated)
  Verdicts/  14 files    EMPIRICAL COLUMN: query mirrors, kernel pins, the runner
  Archive/    17 files   superseded developments, kept for the record
benchmarks/   41 dirs    the input suite (34 certified + 7 declined: shield_unreachable and six
                         declined after the static-reposition removal)
scripts/                 instance generators + build orchestration
docs/                    CERTIFICATION-CHECK.md, READING-GUIDE.md, audits, records
```

**The separation that matters.** `Instances/` *states* theorems; `Verdicts/` makes their
hypotheses empirically checkable **without any possibility of drift**, because kernel
identity theorems tie the runner's printed queries to the theorems' named queries. You can
re-run the oracle without trusting that anyone kept two copies of a query in sync.

---

<a name="file-guide"></a>
## File guide — what each file is *for*

### `Core/` — shared machinery, below both columns

* `FlowCert.lean` — the flow-certificate record: what a per-segment differential-invariant
  claim *is*, independent of how it was obtained.
* `QFrac.lean` — a structural rational (`QF`) whose arithmetic the kernel can actually
  reduce. Exists because Lean's `Rat` normalizes through gcd, which `decide` cannot chew
  through; numeral facts about parsed literals would otherwise be unprovable in-kernel.
* `Reify.lean` — turning syntax into semantic objects, the shared direction both columns
  need.

### `Trusted/` — the tool (inside the trust base only via parser + printer)

* `Parse.lean` — the strict DSL parser. Its contract is *reject, never repair*: a
  malformed model is an error, never a silently weakened one.
* `KeyAudit.lean` — the gate that closes the parser's one structural hole. `Parse.lean`
  reads a fixed key set and ignored unknown keys, so a key it did not know (`reset = …`)
  would be dropped and the file would certify as a model it is not. `auditKeys` whitelists
  per section and `readProblemStrict` refuses anything else, wired into every CLI entry.
* `Smt.lean` — the SMT IR (`ITerm`/`IForm`) and **the printer** (`toScript`). The printer
  is in the trust base: Z3 reads text, and this is what writes it.
* `Oracle.lean` — `z3solve` (an opaque constant) and **the single axiom**
  `z3_unsat_sound`. Also `flow_certified`, which turns a verdict into an invariance fact —
  the one place the oracle enters the proofs.
* `Z3.lean` — the Z3 process session (warm, budgeted). Engineering, not trust.
* `Run.lean` — the lowering: DSL → SMT IR → host terms (`lowerE`, `lowerF`, `dynOf`,
  `invToG`). The bridge between the file's syntax and the proofs' objects.
* `JointVars.lean` — the joint variable list (left variables, then right-only ones), so
  a right side may declare a variable the left lacks (`shield_unreachable`'s `w`).
* `NonConnQuery.lean` — the two non-connection (pruning) queries of a declared right
  edge, defined once; `nonConnPrune`, the verdict runner and the kernel bridge all
  call it.
* `OracleAPI.lean` — **the untrusted search**: stratified segment checking, checked cuts
  (O1/O2), dynamic repositions, cover exploration, and the `--emit-*` doors. Everything
  here only proposes; nothing here is believed.
* `ViabilityEmit.lean` — the emission door for per-face strict/growth tags, feeding the
  existence machinery.
* `EmitIR.lean` — emits the drift-checked `BenchIR` literals.
* `InvComponents.lean` — splitting a multi-conjunct relational invariant into components.

### `Checker/` — certified checking (what replaces trusting the search)

* `Cover.lean` — cover graphs, `RightReach` (right coexecutions), `SegPreservesOn`, and
  `decideCovered`: the decision the kernel replays per benchmark.
* `Checker.lean` — `decideCovered_sound`: a `true` replay *yields* the `Covered` fact.
  This lemma is the hinge that makes the search untrusted.
* `EvolStrengthening.lean` — cut-certificate data (`cutAtoms`, `cutAtomG`, routes) plus its
  kernel well-formedness check.
* `WellFormedChecker.lean` — `decideWellFormed` for settling models: decidable, no Z3, no
  ODE reasoning (see [well-formedness §5](#well-formedness)). `TerrainChecker.lean` and
  `AffineChecker.lean` are the same idea for terrain and affine model shapes.
* `Faithful.lean` — the instance-versus-file identity checks.
* `CoverEmit.lean` — the emitted-cover format shared by tool and instances.
* `NonConn.lean`, `Cover/Coexec.lean`, `Cover/Encoding.lean` — auxiliary certified checks;
  `Cover/Encoding.lean` is where `theorem3Form` and `rvalid_of_encoded_unsat` live.

### `Proofs/Encoding/` — the ∀∃ chain (the paper's proof, mechanized)

*The through-line: a joint flow certificate becomes a per-segment coupling; couplings
compose into a window response; window responses compose into a loop that closes.*

* `Reification.lean`, `JointBridge.lean`, `BridgeUnit*.lean`, `BridgeDischarge.lean`,
  `BridgeFinish.lean` — the transition-faithful core: joint certificates become bounded
  per-segment couplings, and the right automaton is reified as a program.
* `BridgeReposition.lean` — the clocked segment (`clockedSeg`), the bounded coupling
  (`faModalB`), multi-segment lockstep composition.
* `MultiSeg.lean`, `UniformMultiflow.lean`, `UniformFvDischarge.lean` — the clocked
  ε-window chain (`windowSeg`), its `Hmulti` assembly, and footprint dischargers.
* `RepositionDischarge.lean`, `RepositionFinish.lean`, `RepositionEndToEnd.lean` —
  cert-sourced reposition couplings and their end-to-end composition.
* `RepoPrefix.lean` — **reposition-opened windows**: frozen-left hops replay at the left
  endpoint, and hop paths fold into the first piece's coupling.
* `RepoPrefixR.lean` — right-only hops whose vars-disjointness is *derived* rather than
  assumed. This is what unblocked windows with more than one piece: the earlier lemma's
  disjointness hypothesis turned out to be unsatisfiable for real hops.
* `EnvelopeChain.lean` — the envelope-carrying loop invariant (`phiInvE`), the LR-split
  envelope (`envLR`), and `theorem3_faithful_multiE_LR`, the multi-mode modal top theorem.
* `EnvelopeChainM.lean` — the same chain over a **list** of invariant components (`FM`,
  `canonInvM`, `theorem3_faithful_multiF_LR`), for the 19 multi-component benchmarks.
* `EnvelopeChainR.lean`, `ModeRegion.lean` — the mode-region loop invariant: responses
  that owe a landing *region*, not merely an invariant.
* `ModeHandoff.lean` — **the mode-keyed Theorem 3**: the left automaton over the file's
  `next` lists (jump-then-flow, with a fresh left mode variable), the invariant
  `⋀_m (u_L = m → φ_inv(m))`, and `theorem3_modeKeyed` composing per-left-mode steps with
  the cross-mode handoffs; `handoff_of_unsat` bridges the runner's handoff query.
* `WindowRF.lean` — the k > 1 window assembly over list-valued invariants.
* `Reparam.lean` — λ-stretched right runs have exactly the runs of λ = 1 ones, so the
  theorem can be stated at the real automaton (21 benchmarks have a cover window at
  λ ≠ 1).
* `SplitCoupling.lean` — intra-window mode switching (B-then-A at a fixed fraction); the
  five `dt ≤ 1/5` switch instances.
* `WindowGrowth.lean` — the **catch-up** device. The key observation: the `⟨…⟩` side of
  `faModal` runs *after* the left window finishes, so a response may be pure right-side
  flow. `windowSeg_growth` bounds how far a left window can move a quantity,
  `windowSeg_mask` carries the right state through it untouched, and the invariant is
  re-established by arithmetic at the endpoint. Behind the five Z3-free instances.
* `SinkExtension.lean` — a pruned emergency sink appended to the right automaton: the
  original step provider transfers to the enlarged graph with the mode region `⊥` at the
  sink (`docs/PRUNING.md`).
* `NonConnBridge.lean` — the runner's two pruning queries are exactly the hypotheses of
  `nonconn_sound` (Theorem 2); `nonconn_of_unsat` composes them.
* `CanonicalInv.lean` — the canonical relational invariant and its encoding identity.
* `CoverExtract.lean`, `CoverMulti.lean`, `CoverInstance.lean` — from the checker's
  `Covered` facts to theorem-grade responses, including multi-component certificates.
* `ClockedTop.lean`, `FvDischarge.lean`, `ClockReduce.lean`, `CSFBridge.lean`,
  `EncodingBridge.lean`, `LoweringSide.lean`, `ToolLevel.lean` — the settling (cadenced)
  chain and shared dischargers. Deprecated for new work; the settling battery still rests
  on it.

### `Proofs/Flow/` — analysis (existence and invariance facts)

* `PicardBridge.lean` — Picard–Lindelöf delivered into `Program.sem` runs, plus gluing and
  ball-Lipschitz data for polynomial fields. Also `lie_affine_coord` / `lie_two_coord`, the
  Lie derivatives of one- and two-coordinate affine functions.
* `StratifiedBarrier.lean` — the R4 fix: **sequential, acyclic** differential cuts, taking
  multi-component route verdicts to simultaneous preservation.
* `BoxViability.lean` — strict-face box viability by a first-exit argument.
* `BoxViabilityBounded.lean` — growth faces with entry budgets, and the budget-telescoping
  chained viability that most instances consume.
* `StratifiedFaces.lean` — face invariance by strata: the strict core first (needing no
  ordering), then non-strict layers on top. Plus the existence consumer most instances use.
* `AffineFaces.lean`, `AffineFaces2.lean` — equilibrium faces via affine relaxation, and
  monotone lower faces chained onto the affine pass. These exist because a face *at* an
  equilibrium (`y ≥ 0` with `y' = −y`) has zero inflow and the strict argument cannot see it.
* `ViabilityWiring.lean` — the bounded existence residual `HExistSegB` discharged from
  viability, and the bounded coupling it feeds.
* `FaceBridge.lean` — faces ⟺ evolve domain, uniform Picard data, contract-witness transfer.
* `WellFormedFlow.lean` — `WellFormedFlow` / `WellFormedFlowB` and the discharge lemmas;
  the docstrings record why the unbounded form is false.
* `MultisegLanding.lean`, `MultisegLandingBridge.lean` — `LandingWellFormed` and the
  landing dispatch.
* `DISuperlevel.lean`, `WFBoundary.lean` — route-C backing and boundary conditions.

### `Proofs/Soundness/` — the cut lift and guard threading

* `CutChannel.lean`, `CutLift.lean` — per-atom staying from O2 verdicts across all four
  routes, the narrowed-query lift, `cut_hcert`.
* `CutCover.lean` — `RightReachG` (guard-gated switching *recorded* in the reachability
  relation), `CoverCertMC`, and `pres_multi_cut`, the cut baton.
* `CutCoverDischarge.lean` — instance-level dischargers, including frozen and
  contract-shape staying.
* `UniformEvol.lean` — the explicit exponential witnesses for contract fields (`contractΦ`),
  which is why watertank needs no existence hypothesis.
* `GuardThreaded.lean` — settling-side guard threading.

### `Proofs/Transfer/` — rescaling and faithfulness

* `Rescale.lean` — the scaling-transfer lemma: a certificate at one scale transfers.
* `FaithfulBridge.lean`, `FaithfulBridgeGuards.lean`, `FaithfulBridgePad.lean` — the
  instance↔file identity bridge, including guard handling and the padding extension for
  benchmarks whose state-variable count is below the ambient `n`.
* `RealEndToEnd.lean` — the settling family's end-to-end composition.

### `Instances/` — the kernel column

* `BenchIR/<name>.lean` — the drift-checked IR literal, one leaf module per benchmark, so
  editing one benchmark re-elaborates only its own column. `BenchIR.lean` aggregates them.
* `BenchCovers/`, `BenchCoversNC/` — emitted cover data with and without cuts.
* `BenchCoverReplay.lean` — the kernel replay of every cover decision (`by decide`).
* `EvolStrengthenings/` — emitted cut certificates plus kernel well-formedness.
* `BenchViability2.lean` — the face census, 1085/1085 suite-wide.
* `<Bench>Modal.lean` (40 files) — the per-benchmark modal Theorem 3 instances. Each one
  defines its left window family, right mode graph, and invariant terms, discharges the
  side conditions, and applies the generic top theorem.
* `ModalBattery.lean` — imports all of them and re-emits their axiom audits on every
  build, so the audit cannot drift from the theorems.
* (`WatertankModal.lean` / `WatertankViability.lean`, the former flagship, were deleted on
  2026-10-09: `suite_uniform/watertank` is DECLINED since the static reposition was removed.)
* `Throughout/`, `CutThroughout/` and their batteries — the 23 cut-free and 11 cut-lifted
  throughout instances (generated).
* `AxiomCheck.lean` — the chain-level audit showing exactly where `z3_unsat_sound` enters
  (`flow_certified`, `segPres_from_flowCert`, `cut_hcert`) and where it does not.
* `FaithfulCerts.lean`, `SettlingInstances.lean`, `RealInstances.lean`, `UniformPilot.lean`
  — benchmark-identity certificates, the settling battery, and the uniform-route pilot.

### `Verdicts/` — the empirical column

* `Mirrors.lean`, `Combinators.lean` — query mirrors with their `toHost` bridges.
* `GenericPins.lean` — the pins that make a runtime-rebuilt query denote *exactly* the
  hypothesized one: one lemma per query shape, covering all benchmarks at once.
* (`Watertank.lean`, the former flagship's identity theorems, and the `Run.lean`
  watertank phase were deleted on 2026-10-09 with `suite_uniform/watertank`.)
* `ModalPins.lean` — the same idea for the modal instances: an IR query rebuilt at
  runtime denotes the host-level query the hypothesis names.
* `ModalVerd.lean` — states, at the host level, exactly what the runner builds:
  `modalVerd` for the `∀`-over-components form (with an optional head prepended — a
  ceiling or the repaired `Hold` region — or appended), `modalVerd1` for the bare
  three-route disjunction two instances use.
* `ModalPinTable.lean` — the `rfl` pins, one per verdict pack (30 base packs and the 5
  packs of the mode-keyed instances). Each says the instance's own `Verd…` *is*
  `modalVerd` at the arguments the runner's table names, so a wrong table entry fails
  to compile rather than sending Z3 a lookalike query and reporting it green.
* `ModalTablePins.lean` — pins the rest of the `RunInfo` row as data, including the
  `(left, right)` pairs via `RunModal.modalPairs` (the runner's own function, not a
  copy). Corrupting a table field fails the build.
* `ModalCodePins.lean` — pins the runner's *code*: that `(lamN, lamD)` denotes
  `lamN/lamD`, that the ceiling and tail fields build the head terms the instances name,
  and that the three routes tried per component are A, B and C. Breaking any of those
  lines fails the build; before this file they compiled clean.
* `Coverage.lean` — the declared per-phase query counts. A runner that issues fewer
  queries than it owes prints nothing but `UNSAT` lines, so the count is checked rather
  than inferred; a mismatch either way fails `--run-verdicts`.
* `CoveragePins.lean` — proves those declared counts equal what the tables actually
  generate, so the constants and the suite can only change together. Editing one without
  the other fails the build.
* `RunHandoff.lean` — the cross-mode handoff phase: one static query per declared left
  transition, built by `Trusted/Handoff.lean` (the same `IForm` the composition theorem's
  `handoff_of_unsat` denotes); declared failure set in `Coverage.expectedHandoffFailures`.
* `RunNonConn.lean`, `NonConnPins.lean` — the non-connection phase: for every pruned
  edge of every emitted cover, the two pruning queries rebuilt from the emitted IR and
  cut certificate (declared counts `prunedEdges`/`nonconn` in `Coverage`, derived in
  `CoveragePins`), and the pin that the rebuilt pair IS the instance's `VerdNC`.
* `RunCut.lean`, `RunModal.lean` — the runner behind
  `relcert --run-verdicts`. `RunModal`'s `RunInfo` table is the data the pins check;
  `dim`/`invRow`/`order` are quoted out of it by the pins rather than restated.

### `Archive/` — kept for the record, not imported

Superseded pilots and retired routes, plus `RoverLandingInstance.lean`, which contains the
mechanized counterexample `WellFormedFlow_rover_false`. See `RelCertifier/Archive/README.md`.

---

## Lean mechanization ↔ the paper's formal results

| paper result | mechanization | notes |
|---|---|---|
| Theorem 3 (relational ∀∃ over co-executions, reposition-opened windows) | `theorem3Form` + `theorem3_faithful_multiE_LR`; instantiated 41× (base), plus the 7 mode-keyed and 2 cut-composed forms | the loop invariant is the paper's invariant ∧ mode-validity ∧ the joint envelope |
| per-segment flow certificates (three DI routes) | `flow_cert_sound` (A), `flow_cert_sound_strict` (B), `flow_cert_sound_superlevel` (C) in `Core/FlowCert.lean`; `flow_certified` (`Trusted/Oracle.lean`) is the verdict→invariance step; stratified multi-component form in `StratifiedBarrier.lean` | the mutual-narrowing variant was found **unsound** (R4) and replaced by sequential cuts — a tool fix surfaced by the mechanization |
| checked guard cuts (O1 entry / O2 invariance) | `CutLift.lean` per-atom staying + `CutCover.lean` baton | O2's one-sidedness covers both joint and frozen-left flows |
| non-connection certificates (Theorem 2, Section 4.3) | `nonconn_sound` (`Checker/NonConn.lean`), instantiated for `match_multi_rate`'s pruned edge from the runner's two queries (`NonConnBridge.lean`, `MatchMultiRatePruned.lean`); the pruned edge is dropped from `retainedSucc` in the kernel cover replay and never taken by the modal witness | exercised by one benchmark; the obstacle elsewhere is the admissibility of initial modes (`docs/PRUNING.md`) |
| response existence (non-blocking flows) | strict faces + growth budgets (`BoxViability*.lean`), contract witnesses (`UniformEvol.lean`) | the `∀s` form of the side condition is **unsatisfiable in general**; the clock-capped `HExistSegB` is what the coupling consumes |
| cover soundness (the certificate checker) | `decideCovered_sound`, `check_sound_multi{,_cut}` | search untrusted; decisions kernel-replayed per benchmark |
| settling rounds (the cadenced presentation) | `theorem3_faithful_settling` + the 40-benchmark `_real` battery | retained; superseded for new work by the modal chain |

---

## Re-checking the guarantees

```bash
lake build                                      # kernel-checks every instance (~13 h)
./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt
                                                # certification re-run + all hypotheses
BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test
                                                # IR drift, parser, printer, z3 layer
```

The two halves of `--check-quick` are also available separately as
`relcert benchmarks/…/input.txt` and `relcert --run-verdicts`; `relcert --help` lists
everything. **Set `BENCH_PATHS`** when running `relcert-test` — a TSV of
`<benchmark name><TAB><absolute path to input.txt>`. Without it the binary skips its two
Z3-determinism checks; it says so in the final line (`ALL PASS (2 SKIPPED …)`), but a
complete run prints a bare `ALL PASS`.

The full recipe — what each command proves, what it does *not* cover, the cost, and the
per-benchmark table — is [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md).

<a name="trust-audit"></a>
### Trust audit

```lean
#print axioms RelCertifier.MatchMultiRateModal.match_multi_rate_modal
-- + RelCertifier.z3_unsat_sound                     (named verdicts)
#print axioms RelCertifier.Rover3M1Modal.rover3_M1_modal
-- [propext, Classical.choice, Quot.sound]           (Z3-free instance)
#print axioms RelCertifier.pres_multi_cut            -- 3 axioms (pure chain)
```

All 46 theorems of the battery at once:

```bash
lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A3 "depends on axioms"
```

Measured 2026-07-31: 42 theorems at the standard three plus `z3_unsat_sound`, 5 at the
standard three alone, **no `sorryAx`, no `native_decide`, nothing else**. Measured
2026-10-08 (branch `cut-composition`): 59 theorems, 46 with `z3_unsat_sound`, 13 at the
standard three alone. Measured 2026-10-08 after the suite deduplication (branch
`dedupe-suite`): 50 theorems, 40 with `z3_unsat_sound`, 10 at the standard three
alone (the 5 Z3-free base instances, the 3 composed rover theorems, the 2 `…_declared`
theorems). Measured 2026-10-08 (branch `pruning-suite`): **52 theorems, 42 with
`z3_unsat_sound`, 10 at the standard three alone** (the two new ones,
`match_multi_rate_pruned` and `match_multi_rate_nonconn`, both carry the verdict axiom).
Measured 2026-10-09 after the static-reposition removal: **46 theorems, 36 with
`z3_unsat_sound`, 10 at the standard three alone** (the six removed base theorems all
carried the verdict axiom), no other axiom.
Use `-A3`: a four-axiom list prints over four lines and `-A2` drops the line naming
`z3_unsat_sound`.

---

## Soundness findings

Mechanizing surfaced real issues; each is recorded in `docs/COVER-AUDIT.md`:

* **R4 — circular multi-barrier narrowing** (a real tool bug): mutual narrowing of sibling
  components is unsound (the `t²` pathology); fixed by sequential acyclic differential
  cuts. 14 benchmarks transiently declined, all recovered.
* **Unconditioned existence** (`∀ν HExistSeg`, and `WellFormedFlow`'s `∀s` clause) is
  **false in general** — mechanized as `WellFormedFlow_rover_false`. Replaced by the
  envelope-conditioned, clock-capped bounded forms.
* **`Hmulti_window_prefixed`** is unusable for real reposition hops: its vars-disjointness
  hypothesis is unsatisfiable. Replaced by `RepoPrefixR.lean`, which derives disjointness.
* **The parser silently dropped unknown keys** — a model could certify as something it is
  not. Closed by `Trusted/KeyAudit.lean`.
* **Kernel-reduction limits**: `String.startsWith` and the numeral parser are not
  kernel-reducible; the working recipe for lowered-literal facts is elaborator-side `simp`
  with per-numeral facts plus `norm_num`, and `QFrac` for the arithmetic.
* **Route C subsumes the bespoke contract-shape check** — a tool simplification.

---

## Benchmarks

`benchmarks/suite_uniform/<name>/input.txt` — one file per benchmark: state variables,
`L`/`R` mode lists (`ode`, `guard`, `evolve`, `next`), per-mode relational invariants, and
the λ stretch range. 41 directories: 34 certified; six declined after the
static-reposition removal (2026-10-09: `arm_chain_rung1`, `arm_chain_rung2`,
`arm_fidelity_low`, `robot_braking`, `rover3tier_M1`, `watertank`); and `shield_unreachable`, which the
tool DECLINES (its `Shield` guard is a closed compound band the non-connection
certificate does not prune, and `Shield` is an admissible initial mode) and which is
therefore outside the certified suite. The families are watertank, arm control loops, rover refinement ladders, and
terrain and rollover stories up to 12 degrees of freedom; six byte-identical duplicates
were removed on 2026-10-08 (`docs/SUITE-DEDUPE.md`). Format details:
[`benchmarks/README.md`](benchmarks/README.md).

## Further reading

**Start with [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md)** — the entry point to the
whole repository, in dependency order, with the live theorem chain traced end to end and
the historical routes clearly marked.

* [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md) — how to check the suite end
  to end: the checks, the commands, the expected output, the cost, the per-benchmark table.
* `docs/PAPER-MAPPING.md` — paper ↔ mechanization inventory and the R-series gate glossary.
* `docs/COVER-AUDIT.md` — tool↔proof findings.
* `docs/VERDICTS.md` — the empirical report and the full-suite closure record.
* `docs/SUITE-DEDUPE.md` — the 2026-10-08 suite deduplication: method, removals, the 40-benchmark theorem table.
* `docs/PRUNING.md` — the non-connection pruning suite: design rules, the candidate runs, `match_multi_rate`'s exhibit, the `shield_unreachable` outcome.
* `docs/ASSET-MAP.md` — the load-bearing theorems.

Design proposals, nothing scheduled: `docs/proposals/FIXPOINT-DESIGN.md`,
`docs/proposals/RESET-MAPS-SCOPE.md`, `docs/proposals/ROTATION-SCOPE.md`. Completed records live in
`docs/history/`; superseded designs in `docs/archive/`.

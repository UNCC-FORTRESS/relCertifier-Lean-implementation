# relCertifier-lean

A **formally verified** relational-invariant certifier for pairs of hybrid programs,
mechanized in Lean 4 on top of [dL-lean](https://github.com/UNCC-FORTRESS/dL-formalization-Lean)
(`v0.1.0-DI`) and [dL-rel](https://github.com/UNCC-FORTRESS) (NFM'25 encoding).

It matches the functionality of the Python `relCertifier` prototype — certify a supplied
relational invariant between a left (deployed) and right (reasoning) hybrid system via
UNSAT-of-negation with Z3-NRA — but **every soundness-critical function is proven
correct**, each proof citing a mechanized theorem of the imported theory. The single
trusted assumption of the whole tool is that Z3's `unsat` verdict is sound
(`z3_unsat_sound`); everything else is kernel-checked.

## Imported theories — the four repos it builds on

relCertifier-lean proves nothing about differential dynamic logic from scratch; it **composes
already-mechanized theories**. Every soundness-critical lemma cites a theorem from one of these:

| Repo | Pin | What it provides | Key theorems used here |
|---|---|---|---|
| **[dL-lean](https://github.com/UNCC-FORTRESS)** | `v0.1.0-DI` | Core dL: syntax `Term`/`Formula`/`Program`, semantics `Term.eval`/`Formula.sat`/`Program.sem`, and the **differential-invariant** calculus | `DI_strict`, `DI_nonstrict_domain`, `Lie`, `Lie_eq_fderiv`, `hasDeriv_g_along_flow`, `sem_ode_iff_integralCurve`, `nonstrict_boundary_insufficient` (the `t²` soundness countermodel) |
| **[dL-rel](https://github.com/UNCC-FORTRESS)** (NFM'25) | path-req | The **relational (bi-state) extension** of dL and its host **encoding** | `RFormula`, `encode`, `faShape` (the ∀∃ relational modality `[|(α,β)⟩⟩ψ`), `encoding_correct` / `encoding_correct_exists` (**Theorem 2**) |
| **dL-caltiming** (CSF'25) | `v0.1.0-CSF25` | The **∀∃ endpoint modality** `faModal` and its ODE / composition rules (the timed relational calculus) | `faModal`, `faModal_ODE_G`, `faModal_LOCK`, `faModal_MULTI`, `faModal_seq`, `plantT` |
| **Mathlib** | (bundled) | Real analysis + ODE existence | `IsPicardLindelof` (Picard–Lindelöf), `ContDiff`, `isCompact_univ_pi`, `IsCompact.elim_finite_subcover`, `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` |

The dependency flow: **Mathlib** (analysis) → **dL-lean** (dL + `DI`) → **dL-rel** (bi-state
encoding) and **dL-caltiming** (∀∃ modality) → **relCertifier-lean** (this repo: certifier + witness).
dL-rel and dL-caltiming are consumed offline via a `path`-require into `../dL-rel/.lake/packages`;
dL-lean is pinned transitively through dL-rel.

## What is verified

The tool is built bottom-up as three verified local certificates plus their composition,
then a runnable front-end.

| Stage | File | Function(s) | Correctness theorem | Cites |
|---|---|---|---|---|
| **1. Flow certificate** | `FlowCert.lean` | `tderiv`, `lieDeriv`, `flowQuery` | `flow_cert_sound` / `_strict` / `_superlevel` | `DI_nonstrict_domain` / `DI_strict` / `DI_nonstrict_superlevel` |
| **2. Non-connection** | `NonConn.lean` | `lieAlong`, `sourceCheck`, `barrierCheck` | `nonconn_sound` | dL-lean `DI_strict` (Nagumo barrier) |
| **3. Cover / Theorem 3** | `Cover.lean`, `Cover/Encoding.lean` | `Covered`, `RightReach`, `cover_sound` | `cover_sound`, `theorem3_encoded` | flow + nonconn + dL-rel `encoding_correct` |
| **4. Runner** | `Parse.lean`, `Run.lean`, `Main.lean` | parser + Z3-driven cover | — (trusted IO) | uses the verified queries |

The load-bearing new proof is **`tderiv_correct`**: the syntactic partial derivative of a
term denotes its analytic partial derivative (`HasDerivAt`, by induction on `Term`,
product rule ↦ `HasDerivAt.mul`). It is what connects the computed Lie derivative to
dL-lean's semantic `Lie`, and thereby to the differential-invariant theorems `DI`.

**`cover_sound`** is the paper's Theorem 3 (`ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`): by induction
on the assembled right response, each segment preserves the invariant (`flow_cert_sound`,
a time-unbounded `BoxLe`), a jump cannot follow a pruned edge (`nonconn_sound`), and the
budget strictly decreases each step (`cover_budget_decreases` — the mechanized rejection
of budget-neutral cycles, the load-bearing finiteness argument).

## Lean files → paper results

Every source file, its job, the paper result it mechanizes, and the imported theorem it rests on.

| File | Purpose | Paper result | Rests on |
|---|---|---|---|
| `FlowCert.lean` | `tderiv`/`lieDeriv`/`flowQuery` + `flow_cert_sound`/`_strict` | per-segment sync (Lie) obligation | dL-lean `DI_nonstrict_domain`, `DI_strict` |
| `DISuperlevel.lean` | `flow_cert_sound_superlevel` | marginal `ġ=0`-on-boundary energy/contraction class | dL-lean `DI_nonstrict_superlevel` (no subtangency) |
| `NonConn.lean` | `sourceCheck`/`barrierCheck` + `nonconn_sound` | Guard-Boundary-Crossing / edge pruning | dL-lean `DI_strict` (Nagumo barrier) |
| `Cover.lean` | `Covered` (Def. 4), `RightReach`, **`cover_sound`** | **Theorem 3** `ϕ_inv → [|(L*,R*)⟩⟩ϕ_inv` | flow + nonconn certs |
| `Cover/Encoding.lean` | `theorem3_encoded`, `rvalid_of_encoded_unsat` | global ∀∃ validity from Z3 UNSAT | dL-rel `encoding_correct` (**Theorem 2**) |
| `Cover/Coexec.lean` | `CoexecInvThroughout`, `cover_sound_throughout` | cover ⟹ co-execution invariant throughout | `cover_sound` |
| `Checker.lean` | `decideCovered`, **`check_sound`** | `CERTIFIED` ⟹ the ∀∃-throughout invariant | `cover_sound_throughout` |
| `CSFBridge.lean` | `faModal_ODE_G'` | domain-restricted ∀∃-ODE base rule | dL-caltiming `faModal_ODE_G` |
| `Reify.lean` | `segment_faModal`, `segment_relational` | one cover segment ⟹ a CSF ∀∃-ODE guarantee | `faModal_ODE_G'` |
| `Reification.lean` | mode-list ⟹ choice/star programs | assemble `(L*, R*)` from the parsed automata | `faModal` choice/seq rules |
| `MultiSeg.lean` | `multiseg_het`, `hstep_multiseg_het` | B>1 multi-segment mode-switching witness | dL-caltiming `faModal_MULTI`, `plantT` |
| `ClockReduce.lean` | `clockReduce` | the timing clock is an eliminable proof device | dL-lean `sem`, `Term.coincidence` |
| `EncodingBridge.lean` | `faModal_to_faShape`, `relational_loop` | CSF `faModal` ⟹ NFM'25 `faShape` = `[|(L,R)⟩⟩ψ` | dL-rel `sat_encode_faShape`, `encoding_correct` |
| `PicardBridge.lean` | the `hExist` witness (existence + invariance + chaining) | discharges the ∀∃ duration-existence side-condition | Mathlib `IsPicardLindelof`; dL-lean `sem_ode_iff_integralCurve` |
| `HExistDischarge.lean` | `hExist_from_rover`/`_cubic` | thread the witness into `segment_faModal` (masking seam) | `PicardBridge`, `Reify` |
| `ToolLevel.lean` | `certified_relational`, `pair_faModal` | tool-level: a Z3 verdict ⟹ the paper's ∀∃ modality | Encoding + Reify + `z3_unsat_sound` |
| `Oracle.lean` | `z3_unsat_sound` (the one axiom) + `flow_certified` | the trusted SMT leaf | — (axiom) |
| `Smt.lean` / `Z3.lean` / `Parse.lean` / `Run.lean` / `Main.lean` | computable IR + SMT printer, Z3 session, parser, runner, `relcert` exe | trusted IO shell | uses the verified queries |

## The main soundness result — the cover (Theorem 3)

The whole tool exists to discharge one theorem. Here it is, verbatim (`Cover.lean`):

```lean
theorem cover_sound (G : SearchGraph V) (g : Term V) (cert : CoverCert G g) :
    ∀ cfg ν ω, Covered G cfg → RightReach G cfg ν ω → InvHolds g ν → InvHolds g ω
```

**In words.** Fix a relational invariant component `g ≤ 0` (`InvHolds g`). `Covered G cfg` is the
paper's **Definition 4** — a purely combinatorial fact about the mode graph `G`: from configuration
`cfg = (right mode q, budget B)`, either the budget is closed in this residence (`base`), or **every
retained successor** covers the decremented budget (`step`). `RightReach G cfg ν ω` is the actual
∀∃ **right response**: starting at `ν`, the right system stays put, flows within a mode (time-unbounded —
the flow certificate is a *forward* invariant, not a bounded check), or jumps along a declared successor
whose guard the evolved state enables. `cover_sound` says: **if the graph is covered and the invariant
holds at the start `ν`, it holds at every reachable right-response endpoint `ω`.** That is exactly the
paper's Theorem 3 conclusion — *for every left execution there exists an admissible right response that
keeps the relational invariant within tolerance, throughout*.

The proof is an induction on `RightReach`: the `evolve` case is discharged by `cert.segPres` (the
per-segment flow certificate `flow_cert_sound`, itself citing dL-lean's `DI`); the `jump` case uses that
the jump's budget gate `m.weight < B` matches `Covered`'s `step`, so the target config is still covered,
and that a pruned edge (via `nonconn_sound`) is never taken. **Budget strictly decreases each residence**
(`cover_budget_decreases`) — the finiteness argument that rejects budget-neutral cycles, the reason the
star `(L*, R*)` terminates.

**From the local theorem to the global ∀∃ claim — the encoding.** `cover_sound` is a statement about
one host-dL invariant `g` along right responses. The paper's actual guarantee is a **relational
(bi-state)** formula `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`, a sentence of dL-rel about *pairs* of states. Two
mechanized bridges connect them:

1. `faModal_to_faShape` (`EncodingBridge.lean`) lifts the CSF endpoint modality `faModal` (what a
   covered segment yields) to dL-rel's **`faShape α β ψ = [|(α,β)⟩⟩ψ`** — the NFM'25 ∀∃ relational
   modality — via the proven `sat_encode_faShape` (with the identity renaming `ρ = id`, since the joint
   system already binds disjoint `Side.L`/`Side.R` coordinates).
2. `theorem3_encoded` (`Cover/Encoding.lean`) closes the loop to Z3: a **single `unsat`** of the encoded
   negation `encode ρ (¬ theorem3Form L R ϕ_inv)` implies `RFormula.rvalid (theorem3Form …)` — the
   bi-state validity of the global claim — by dL-rel's **`encoding_correct` (Theorem 2)**, which states
   that bi-state truth of a relational formula equals host-dL truth of its encoding at a bridged join
   state. So the tool's `CERTIFIED` (`check_sound` ⟹ `cover_sound_throughout` ⟹, with the encoding,
   `rvalid`) **provably implies the paper's ∀∃ relational invariant on the mechanized relational logic** —
   not a bespoke re-statement.

**Where dL-rel does the load-bearing work.** dL-rel is not a convenience import; it is what makes the
∀∃ fragment expressible and the encoding sound. `faShape`/`encode` were built for exactly this modality,
and `encoding_correct` is the one theorem that turns "Z3 said `unsat`" into "the relational sentence is
valid." The single trusted assumption remains `z3_unsat_sound`; the bridge itself is a proven dL-rel
theorem.

### Trust boundary

```
#print axioms cover_sound          -- propext, Classical.choice, Quot.sound
#print axioms nonconn_certified    -- + z3_unsat_sound
#print axioms flow_certified       -- + z3_unsat_sound
```

The pure core depends only on the three standard Lean axioms. The IO-boundary theorems add
exactly one leaf, `z3_unsat_sound` (an `unsat` verdict from the opaque `z3solve` is sound),
isolated in `Oracle.lean`. **No subtangency axiom** — where the Python tool's boundary-only
non-strict flow check is unsound (dL-lean's `nonstrict_boundary_insufficient`, the `t²`
counterexample), the verified version takes the sound strict route (`DI_strict`).

## Soundness findings

Carried through every stage: a **boundary-only non-strict** check (`ẋ ≤ 0` on `{g=0}`
alone) is unsound without a regular-boundary hypothesis. The tool therefore certifies via
either the domain-wide non-strict route (`DI_nonstrict_domain`) or the strict-boundary
route (`DI_strict`), never the unsound one — declining where only the unsound route would
succeed. Pruning is one-sided: an edge is dropped only on a trusted UNSAT; failing to
prune is safe by default.

## The oracle (for invariant-synthesis search)

Built to be called thousands of times in a synthesis loop. Three **distinct, never-
conflated** outcomes — the honesty boundary a search depends on:

| outcome | meaning | synthesis reads it as |
|---|---|---|
| `CERTIFIED` | the **verified** `decideCovered` accepted the cover (⟹ `check_sound` ⟹ the ∀∃-throughout invariant), every segment discharged by a sound-route UNSAT | a real, sound YES |
| `DECLINED` | all queries definitive `sat`/`unsat`, no cover closes | a real, sound NO |
| `ERROR msg` | any harness/solver/env failure (missing Z3, crash, malformed, `unknown`/timeout, unlowerable) | retry / abort — never learn from it |

An `ERROR` can never masquerade as a verdict: `CERTIFIED` is only ever produced by actual
`unsat`; an inconclusive/failed query surfaces as `ERROR` when a covering route needed it.

**In-process API** (link the pipeline directly — no per-call process spawn):

```lean
open RelCertifier RelCertifier.Oracle
-- one warm, persistent Z3 session serves thousands of calls:
def loop (s : Z3Session) (cands : List PProblem) : IO (List Outcome) :=
  cands.mapM (certify s)          -- certify : Z3Session → PProblem → IO Outcome
```

Hermetic + deterministic: Z3 is a **pinned** absolute path (`RELCERT_Z3`, never
PATH-resolved), a **persistent** `z3 -in` process (warm), with `(reset)` + a per-query
`:timeout` + a machine-independent `:rlimit` + an `(echo)` **sentinel** that keeps the pipe
in sync so the same query always gives the same verdict. The cover DFS is memoized so a
large time-stretch can't blow up the pure search. **Warm per-call: mean 49 ms, median
26 ms, p90 101 ms, max 199 ms** (all 46 in ~2–3 s) — dominated by the Z3 solve. Every call
terminates (query / SMT-size / wall / rlimit bounds, all deterministic).

## Running it

```sh
lake build                      # verified library + `relcert` + `relcert-test`
lake exe relcert <input.txt> …  # oracle over each file on one warm session (3-way verdict + ms)
lake exe relcert                # no args: the Stage-1 flow-certificate demo
BENCH_PATHS=<name-tab-path-file> lake exe relcert-test   # trusted-layer test suite
```

## The ∀∃ witness — `hExist` discharged (`PicardBridge.lean`)

The paper's ∀∃ relational modality `[|(L*,R*)⟩⟩ψ` carries a **duration-existence
side-condition** (`hExist`, from dL-caltiming): for every left run there must **exist** a
right run of the matching duration, staying in the right evolution domain. This is the
existential witness of the ∀∃ — carrying it makes the result a ∀-conditional, not a ∀∃.
`PicardBridge.lean` **discharges it by explicit witness construction**, standard three
axioms throughout, **no new axiom, no subtangency, no clock, no `sem`-gating**.

- **Existence** (Mathlib Picard → dL-lean `sem`): `term_contDiff`/`odeField_contDiff`
  (fields are `ContDiff`), `odeField_lipschitzOnWith` (Lipschitz-on-compact),
  `sem_of_integralCurveOn` (the reification seam: a Mathlib integral curve **is** a dL-lean
  `sem` run, via the proven `sem_ode_iff_integralCurve`). Three routes, K/L **proven**:
  `picard_isPL_of` (global-Lipschitz, affine fields), `uniform_local_existence_on_compact`
  + `box_compact` (compactness-subcover), `picard_isPL_of_local` + the s-independence
  establishment (`odeField_sindep` → compact cross-section → uniform K/L) for the nonlinear
  (cubic, degree-3 `v·ψ²`) fields.
- **Invariance** — un-gated raw-curve positive invariance (the piece dL-lean leaves
  `sem`-gated): `strict_invariance_raw` (first-exit, strict), `nonstrict_antitone_raw`,
  `growth_bound_raw`/`_lower`, `asymptotic_invariance_raw` (general-box asymptotic, covers
  attitude `ψ'=−ψ`), and the coupled faces `lie_two_coord` + `coupled_eigen_invariance`
  (eigencoord decoupling — **every coupled subsystem has real eigenvalues, no Lyapunov**) +
  `driven_bound_raw` (defective/critically-damped companions, via `(v−C)e^{λt}` antitone).
- **Chaining** to the full parser duration: `sem_ode_glue`, `RunFor` + algebra, `chainN`
  (uniform step ⟹ finite steps cover `[0,Tᵢ]`).
- **Packaging + relational wiring**: `RunFor_unpack` → the witness shape;
  `hExist_from_rover`/`hExist_from_cubic` thread it into `segment_faModal` through the
  **field-independent cross-side masking seam** (`Rv_not_mem_leftBlock_bound`, `Side.R≠Side.L`:
  the left run freezes the right's coords ⟹ right starts in-slab).

`hsmax_of_left_duration` closes the timing coupling (left domain bounds duration →
`ν si + v_max·s ≤ S_max`) as `left_duration_bound` (analytic, proven) + a Z3-checkable
arithmetic inequality.

## Benchmark suite — instantiation results

The full 46-benchmark suite (from `relCertifier-src`, under `benchmarks/suite/`) run on the
trusted method (Z3 UNSAT-of-negation):

| | count | route |
|---|---|---|
| **CERTIFIED** — source invariant inductive | **35/46** | flow-cert Z3 UNSAT, cover closes (20-step λ grid) |
| CERTIFIED — **restated** (strengthened) invariant | **+7** | `benchmarks/restated/` — 4 rover-family (velocity-coupled) + 3 arm/plant (`θ[l]−θ[r]+v[l]≤d ∧ θ[l]≤θ[r]+d`) |
| CERTIFIED — **faithful successor correction** (dead-edge removal, invariant unchanged) | **+2** | `match_multi_eps`, `rover3tier_M1` |
| **DECLINED** — beyond the reachability-free single-λ cover | **2** | method-scope; tool declines soundly |

**44/46 discharge** (42 on the trusted invariant method + 2 via a faithful successor
correction). **Key finding**: the declines were **method-scope**, not invariant-restatement
gaps — the invariants are correct; the reachability-free all-successors single-λ cover can't
witness the `∃`-response. `match_multi_eps`/`rover3tier_M1`: L `ACCEL` `v'=k(1−v)` asymptotes
to `v=1`, so the `COAST` guard `v≥1` is **never reached** → the `ACCEL→COAST` edge is **dead**;
the all-successors cover required covering it (forcing `v_R→0.2` while `v_L→1`, `Δv→0.8>0.5`).
Removing the dead edge is a faithful **successor-completeness** correction (model-faithfulness
TCB, invariant unchanged) — the sound strict barrier can't prune it (`İ=0` equilibrium at `v=1`,
the `t²`-class boundary).

**The 2 remaining declines are honest, distinct scope boundaries of the paper's Definition-4 cover —
not invariant gaps and not the same failure.** The invariants are correct; the tool declines soundly.

- **`arm_chain_rung1` — the all-successors *conservatism*.** A safe `∃`-response exists (the right
  `Approach` can evolve past its guard, staying alongside the forward-moving left `ApproachFast`). But
  Definition 4 (`Covered.step`) requires **every retained successor** to cover, and the right's
  `Approach→Return` edge is enabled (its guard `θ≥0.7` is genuinely reached), so it is retained — and
  `Return` (θ decreasing) cannot cover the still-forward left. The `∀∃` semantics needs *one* right
  response; the paper's cover proves *all* retained responses safe (sufficient, but stronger). Recovering
  this benchmark would require a **tighter cover** that certifies "some response works" — a *method
  extension* with its own soundness proof, **not** a bug-fix and not the paper's Definition 4.
- **`rover3_M1` — no safe response exists at all.** Its `Drift` mode is uncoverable by **every** right
  mode (all Z3-SAT), so there is no `∃`-response in the reachability-free setting. It needs **budget-aware
  Strategy-2 reachability**, which the universal all-successors cover rejects by design — genuinely out of
  scope. (Not reopened on simulation; Z3-SAT is the trusted signal.)

So the two boundaries are different in kind: one is the *conservatism* of all-successors (a response
exists but the cover over-requires); the other is a *true absence* of any response (needs reachability).
Both are correct declines — the tool **never false-certifies** (Z3-SAT, not simulation, is trusted).

**42/46 on the pure trusted method (Z3 UNSAT).** Instantiation was the in-use check — per benchmark:
shape match (46/46), Z3 query closes, side-conditions (cubic factor `0.5ψ²+0.3θ²∈[0.20,0.39]<1`; coupled
real-eigenvalue) — all confirmed. It **surfaced** the declines rather than forcing them: `arm_chain_rung2`
was a **λ-search limit** (denser 20-step grid certifies it, invariant fine); `arm_refinement`,
`arm_fidelity_low`, `plant_fan_low` were **restatement gaps** (velocity-coupled conjunction, proven to
imply the safety property, certifies via Z3 UNSAT); `match_multi_eps`, `rover3tier_M1` were **dead-edge**
(faithful successor correction). We do **not** force the last two — a `+0.8` invariant on match/rover3tier
certifies but *weakens* the safety property (`v_L≤v_R+0.5`), so it is invalid.

Requires Lean 4 (`leanprover/lean4:v4.31.0`, pinned), a pinned Z3 (`RELCERT_Z3` or a
standard absolute path), and `dL-rel` at `../dL-rel` (transitively provides dL-lean
`v0.1.0-DI` and the encoding bridge). Env: `RELCERT_Z3_TIMEOUT` (ms, default 10000).

## Soundness of `CERTIFIED` — the certified-checker architecture

`CERTIFIED` is **backed by proof**, not by the search. The untrusted cover DFS does not decide
the verdict: the runner builds the abstract `SearchGraph` from the parsed model and gates
`CERTIFIED` on the **verified computable `decideCovered`** — a transcription of the paper's
Definition 4 (`base`: `B ≤ w(mR)` → budget closed; `step`: every retained successor covers at
`B−w`). `decideCovered = true ⟹ Covered ⟹`, with the evolution-domain flow certs as `CoverCert`,
the ∀∃-throughout invariant (`check_sound`, citing `cover_sound`). A search/runner bug can only
make it **reject** — never a false `CERTIFIED`. Residual TCB: the parser and the single Z3
`unsat` leaf.

**Soundness fixes caught while validating (real bugs, `Lean-object ≠ paper-object` class):**
- **Guard-narrowing**: an earlier version conjoined the mode **guard** into the flow-certificate
  domain, narrowing the certificate to a sliver the real flow leaves — a Return mode entered at
  `θ≥0.7` flows to `θ<0.7`, so the query was *vacuously* UNSAT (falsely certified) while
  `ġ=0.7>0` on the real flow. Fixed to the **evolution domain only** (holds throughout the
  segment); the affected benchmarks correctly moved to DECLINED. Only `Run.lean` changed.
- **`Covered` base case** (Definition 4): single-segment covers could not terminate, spuriously
  forcing closed-leaf certification — corrected by the `base`/`step` split.
- **Two parser bugs**: `dynOf` silently defaulted an unlowerable term to `0` (a wrong field
  could falsely certify) — now propagates to ERROR; the tokenizer split `-` inside negative
  literals — now `mergeSigns` re-glues signed literals. Neither had produced a wrong CERTIFIED.

The sound routes: strict / domain / **superlevel** flow certificates (`DI_nonstrict_superlevel`,
proven from vendored Mathlib — **no subtangency**, closes the marginal `ġ=0`-on-boundary
contraction/energy class, rejects the `t²` pathology). The trusted layer is tested
(`relcert-test`): determinism, outcome-integrity (missing Z3 / unparsed / crash → ERROR),
parser, lowering, Z3-layer verdicts. See the **Benchmark suite** section above for the current
42/46 trusted-method tally and the honest decline breakdown.

## Layout

```
RelCertifier/
  FlowCert.lean       Stage 1 — tderiv/lieDeriv + flow certificate soundness
  NonConn.lean        Stage 2 — Nagumo non-connection barrier
  Cover.lean          Stage 3 — cover relation, finiteness, cover_sound (Theorem 3)
  Cover/Encoding.lean Stage 3 — global ∀∃ encoding bridge (encoding_correct)
  Smt.lean            computable IR + SMT-LIB printer (pinned to lieDeriv by bridge lemmas)
  Oracle.lean         the single trusted leaf (z3_unsat_sound) + IO-boundary theorems
  Parse.lean          input.txt parser (trusted IO)
  Run.lean            end-to-end cover runner
  PicardBridge.lean   the ∀∃ witness — hExist discharged (existence + invariance + chaining)
  HExistDischarge.lean cross-side masking seam — hExist into segment_faModal
Main.lean             `relcert` executable
ARCHITECTURE.md       certified-checker architecture + the finding that reshaped it
MAINTHEOREM.md        the CERTIFIED ⟹ ∀∃ soundness chain + hExist ledger
benchmarks/SPLIT.md   full-suite field-shape split (existence-route map)
```

# Paper ↔ mechanization: an inventory

Status: INVENTORY (2026-07-19, main = f85e61f). Produced by a full read of
`RelCertifier/Proofs/**` — every theorem concluding `rvalid (theorem3Form …)` — and every
file in `RelCertifier/Instances/`. It replaces three earlier partial assessments in this
file's history, each of which **understated** what the development proves; §6 records
what went wrong so the mistake is not repeated.

**Suite deduplication (2026-10-08).** The suite is 40 certified benchmarks since six
duplicates were removed (`docs/SUITE-DEDUPE.md`); the per-benchmark tallies in §2c, §3j
and §4 are updated below, and "46" in the quoted historical gates (§6) and dated
measurements is the count of that time.

---

## 1. What the paper asks for

The paper states its obligation in the ∀∃ modality over the `cpsProg` programs:

- **Definition 1**: `φInv → [|(L, R)⟩⟩ φInv`
- **Eq. (relational-invariant)**: one-iteration preservation, `φInv → [|(Lsysi, Rsys)⟩⟩ φInv`
- **Eq. (mode-inv)**: the same, decomposed per left mode
- **Theorem 3** (Soundness of Synthesis): an all-successors cover induces a certified
  witness strategy, hence `φInv → [|(L,R)⟩⟩ φInv`

Target Lean shape: `rvalid (theorem3Form L R φ)` — and `theorem3Form`
(`Checker/Cover/Encoding.lean:51`) *is* that formula, stars both loop bodies, and says so
in its own docstring.

---

## 2. Theorem 3 is mechanized generically, Emit-free, from the checker's own decision

**Three generic theorems take `decideCovered` — the function the tool runs — plus a
Z3-backed `CoverCert`, and conclude `rvalid (theorem3Form …)`. None assumes an emission
device.**

| theorem | where | left shape | note |
|---|---|---|---|
| `decideCovered_implies_theorem3_faithful` | `Proofs/Encoding/BridgeDischarge.lean:176` | one ODE program | also yields the throughout conjunct; **listed in the axiom audit** |
| `theorem3_uniform_from_covered` | `Proofs/Encoding/CoverExtract.lean:122` | list of `windowSeg`s | **R1 gate** — section header *"The top theorem, Emit-free — the checker in the conjunction"*; docstring: *"the ASSUMED `EmitWindows` is GONE"* |
| `theorem3_uniform_guarded` | `Proofs/Encoding/CoverExtract.lean:218` | guard-gated windows, one per left mode | **R2 gate** — each mode's lowered guard carried, so the obligation arises only at guard-satisfying entries |

`decideCovered_implies_theorem3_faithful` also documents exactly what is load-bearing:

> `cert` is required for the `rvalid` conjunct … `hchk` (`decideCovered`) is load-bearing
> for the **throughput** conjunct, NOT for `rvalid`: the `faModal_LOCK` loop preserves the
> invariant over any number of iterations, so the ∀∃ modality needs every mode CERTIFIED
> (`cert.segPres`), not the coverage/budget DECISION.

Axioms: `[propext, Classical.choice, Quot.sound]` — parametric in `cert`, so
`z3_unsat_sound` enters only where the certificate is constructed per mode
(`segPres_from_flowCert` / `flow_certified`). Re-emitted on every build by
`Instances/AxiomCheck.lean`.

---

---

## 2a. Theorem 3, clause by clause

The paper's statement:

> **Theorem 3 (Soundness of Synthesis).** For a left mode `m_L`, if every admissible
> initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`,
> then the cover induces a certified witness strategy for `m_L`. If such a cover exists
> for every `m_L ∈ modes_L`, then `φInv` is a ∀∃ invariant:
> `φInv → [|(L,R)⟩⟩ φInv`.

Against `theorem3_uniform_from_covered` (`Proofs/Encoding/CoverExtract.lean:122`):

| paper clause | Lean |
|---|---|
| *"every admissible initial right mode `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)`"* | `hchk : ∀ q, q < Gj.modes.length → decideCovered Gj fuel ⟨q, B, SrcSetting.preJ⟩ = true` — `q₀ ↔ q`, `ε_L ↔ B` (ℕ-discretized), *pre-joint* `↔ SrcSetting.preJ`, and *all-successors* is `decideCovered`'s own successor case `(G.retainedSucc q).all (…)`, i.e. Definition 4 verbatim |
| *"the cover induces a certified witness strategy for `m_L`"* | **not a hypothesis — the proof.** `emitWindows_self` builds the window response from the declared self-edges and feeds `theorem3_uniform_multiflow`. This is exactly what the **R1 gate** required: the witness *derived* from `Covered`, never assumed (Definition 5 in the paper) |
| *"if such a cover exists for every `m_L ∈ modes_L`"* | `leftData : List (…)`, one entry per left mode, with `hleft : ∀ d ∈ leftData, …`; the left program is `bigChoice (leftData.map (windowSeg …))` |
| *"`φInv → [|(L,R)⟩⟩ φInv`"* | `rvalid (theorem3Form (bigChoice (leftData.map …)) (rightAutomatonBody Gr mv) (ϕinv ∧ mvValidR mv Gr.modes.length))` |

**What the Lean makes explicit that the paper folds in.** The Lean takes
`cert : CoverCert Gj g` — the flow certificates — as a *separate* argument. The paper
folds this into the graph construction (§4.2: *"If no flow certificate is available at
`m_R`, none of its candidate edges is retained"*), so "a cover exists" already
presupposes certificates. Both are the same content; the Lean simply names it.

**What the Lean adds.** A second conjunct, `∀ q, ∀ ν, InvHolds g ν →
CoexecInvThroughout Gj g ⟨q, B, preJ⟩ ν` — the invariant holds *throughout* the
co-execution, not merely at the round's end. The paper's Theorem 3 states only the
endpoint form.

**A decomposition of your own proof, worth knowing.** The Lean proof draws the two
conjuncts from *different* hypotheses, and `decideCovered_implies_theorem3_faithful`
records it:

> `cert` is required for the `rvalid` conjunct … `hchk` (`decideCovered`) is load-bearing
> for the **throughput** conjunct, NOT for `rvalid`: the `faModal_LOCK` loop preserves the
> invariant over any number of iterations, so the ∀∃ modality needs every mode CERTIFIED
> (`cert.segPres`), not the coverage/budget DECISION.

So Theorem 3 bundles two guarantees with two different sources: **invariant preservation**
comes from the flow certificates at every mode, while **duration coverage** — that the
response spans the whole `m_L` residence — comes from the budget walk. The paper's §4.4
("Finiteness and Duration Coverage") is the second; §3's flow certificates are the first.
Stating that split explicitly would sharpen the theorem's proof sketch.

## 2b. Theorem 3 for MODE-DEPENDENT invariants — the composition lemma (2026-10-07)

Seven benchmarks declare one relational invariant per LEFT mode. §2a's clause-by-clause
mapping covers a single `φInv`; the paper's general statement is

> **Theorem 3 (general form).** Let `Φ ≡ ⋀_m (u_L = m → φ_inv(m))`. If (i) for every left
> mode `m_L` every admissible initial right mode admits an all-successors cover at
> `φ_inv(m_L)`, (ii) for every declared left transition `m' → m`,
> `φ_inv(m') ∧ guard_m(x_L) → φ_inv(m)`, and (iii) the well-formedness assumption holds,
> then `Φ → [|(L*, R*)⟩⟩ Φ`.

Mechanized in `Proofs/Encoding/ModeHandoff.lean` as `theorem3_modeKeyed`, clause by clause:

| paper element | Lean |
|---|---|
| the left program `L` with mode variable `u_L`, body `⋃_m ?(m ∈ next(u_L)) ; ?guard_m ; u_L := m ; flow_m` | `leftAutomatonBody A ul` — `bigChoiceP` over `leftModeStep A ul m'` = `?(u_L = m') ; ⋃_{t ∈ next m'} (?guard_t ; u_L := t ; window_t)`. **Jump-then-flow, as the paper writes it** (the right side keeps `modeStep`'s flow-then-jump rotation, `docs/proposals/ROTATION-SCOPE.md`). `A : LeftAut n` is built per benchmark from the IR: `windows` = the clock-capped `windowSeg` of each left mode (the same programs the per-mode theorems quantify over), `guards` = `hostGuard` of each left mode, `next` = the file's `next` lists resolved by the runner's own `Handoff.leftModeIndex` — and each instance proves by `decide` that this graph's transition list IS `Handoff.transitions IR`, the list the handoff runner checks |
| `u_L` | a third `Aux` coordinate `(Aux, 2)` (beside `mv = (Aux, 0)` and the clock `tg = (Aux, 1)`); `rover3_M1` has `n = 2` and is re-lowered at the padded `n = 3` for it |
| `Φ ≡ ⋀_m (u_L = m → φ_inv(m))` | `modeKeyedR ul ϕ nL = ⋀_{m < nL} (⌊u_L = m⌋_L → ϕ m)`, encoding to the host `modeKeyed ul F nL` with `sat_modeKeyed : … ↔ ∀ m < nL, ν u_L = m → sat (F m) ν` |
| the loop invariant | `psiK ul ϕ nL domL domR BkR = ((Φ ∧ envLR) ∧ BkR) ∧ ⌊u_L ∈ modes⌋_L`, where `BkR` is the right-side bookkeeping the per-mode chain carries (`mvValidR` for the F-chain, `mvRegionR` for the region-carrying R-chain) — the same conjuncts §5 already lists as bookkeeping, plus `u_L ∈ modes` |
| **(i)** per-mode all-successors cover at `φ_inv(m_L)` | `hstepM : ∀ t < nL, ∀ σ, sat ((F t ∧ env) ∧ Bk) σ → sat (faModal (window t) R* ((F t ∧ env) ∧ Bk)) σ` — exactly the per-mode `hstep` that `theorem3_faithful_multiF_LR`/`_multiR_LR` consume, produced from the instance's own `Hmulti` provider by `hstepMode_multiF` / `hstepMode_multiR` (each is `hstep_single_multiF/R` for one window) |
| **(ii)** the handoff `φ_inv(m') ∧ guard_m → φ_inv(m)`, DOMAIN-CONDITIONED: at a switch the left state is the end of an `m'` residence (in `evolve_{m'}`) and satisfies `guard_m`, the right state is in its evolve domain | `hhand : ∀ m' < nL, ∀ t ∈ A.succ m', ∀ ω, sat (F m') ω → sat env ω → sat (A.guard t) ω → sat (F t) ω`, with `env = domL ∧ domR` the envelope the loop invariant carries (`hstep_modeKeyed` has it at the switch state). Two discharges: **(a)** from Z3 on the runner's query — `handoff_of_unsat` takes `z3solve (ihandoffQuery …).toHost = unsat` for the very `IForm` `relcert --run-verdicts` prints (`Trusted/Handoff.lean`: `φ_inv(m') ∧ evolve_{m'} ∧ guard_m ∧ evolve_R ∧ ¬φ_inv(m)`, `evolve_R` the uniform right evolve), via `z3_unsat_sound`; **(b)** in-kernel, when the rows are nested (`FM_mono`), constant-offset bounds (`linarith`), or follow from the domain (`rover3tier_rung12`'s `COAST → ACCEL` uses `a_L ≥ −0.3`). All seven composed instances use (b), so they add **no** verdict beyond their per-mode packs |
| **(iii)** well-formedness | unchanged: successor-completeness with guard-gated switching stays the trust item (README § trust); the mechanized side conditions are freshness of `u_L` (`hulF`, `hulenv`, `hulBk`, `hulG`, `hframes`, `hulR`) and the two footprint disjointnesses `hd`/`hddF`, discharged by `hd_modeKeyed` / `hddF_modeKeyed` (`sides_disjoint3`) |
| the conclusion `Φ → [|(L*, R*)⟩⟩ Φ` | `rvalid (theorem3Form (leftAutomatonBody A ul) (rightAutomatonBody G mv) (psiK …))` — the same `theorem3Form` as every other instance |

**Proof shape** (`hstep_modeKeyed`). One iteration of the left automaton from a state
satisfying `Φ`: `?(u_L = m')` selects the current mode, an edge `t ∈ next m'` whose guard
holds is taken, `u_L := t`, `window_t` runs. The handoff (ii) turns `F m'` into `F t` at the
switch state; `u_L` is fresh for `F t`, `env`, `Bk`, so they transport to the post-switch
state; the per-mode step (i) at `t` produces the right response; `u_L` survives the window
(`FramesMv`) and the right response (`Program.bound_effect`, `u_L ∉ bv R`), so the
mode-keyed conjunct at the end reads exactly `F t`, which the response established. The
loop closes by `relational_loop_multi` as for every other instance.

**Mode-independent invariants are the special case** `F m = F` for all `m`: (ii) is
trivial and the statement collapses to the one §2a maps (the 33 mode-independent instances
keep their `bigChoice leftProgs` form, which over-approximates the left and so is the
stronger claim — §5).

### The seven benchmarks

| benchmark | declared rows | handoff (tool, `docs/HANDOFF.md`) | composed Lean theorem | its handoff discharge | axioms |
|---|---|---|---|---|---|
| `rover3_M1` | Drive `+0.5` ⊂ Drift `+1.0` ⊂ Stop `+2.0` | 5/5 unsat | `Rover3M1Handoff.rover3_M1_modeKeyed` (n padded 2 → 3) | `linarith` | standard three (Z3-free) |
| `rover_coupled` | same | 5/5 | `RoverCoupledHandoff.rover_coupled_modeKeyed` | `linarith` | standard three |
| `rover_position` | same | 5/5 | `RoverPositionHandoff.rover_position_modeKeyed` | `linarith` | standard three |
| `story1_attdist_rung_a_6to8` | STEEP = `v[l] ≤ v[r]` ∧ common; MODER = FLAT = common | 5/5 | `Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed` | `FM_mono` | + `z3_unsat_sound` (3 new STEEP packs `VerdS`, 6 base packs) |
| `story1_attdist_rung_b_12dof` | same nesting, region-conditioned (`mvRegionR`) | 5/5 | `Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed` | `FM_mono` | + `z3_unsat_sound` (6 packs `VerdR r m`, `r ≤ m`) |
| `story3_rollover_ladder_rung_b` | same nesting | 5/5 | `Story3RolloverRungBHandoff.story3_rollover_rung_b_modeKeyed` | `FM_mono` | + `z3_unsat_sound` (3 `VerdS` + 6 base) |
| `rover3tier_rung12` (ACCEL row repaired 2026-10-08, rows only) | ACCEL = `v[l] ≤ v[r]+0.5 ∧ 3v[l]+a[l] ≤ 3v[r]+1.2`; COAST = `3v[l]+a[l] ≤ 3v[r]+1.2` (originally ACCEL = `v+0.5 ∧ a+0.8`, under which `ACCEL → COAST` failed — `docs/HANDOFF.md`) | 4/4 (domain-conditioned) | `Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed` (the two per-left-mode theorems stand too) | `FM_mono` / `linarith` with the evolve floor | + `z3_unsat_sound` (the base `VerdQA 0/1`, `VerdQC 0/1`) |

All seven are composed (`rover3tier_rung12` after its row repair). The per-mode theorems the
composition consumes are the base instances' (`respondX`, `esX` reused unchanged) re-stated
at the declared rows: the rover trio's catch-up
response is offset-independent (`HmultiRow r`), the stories' STEEP window gets a new
three-component pack at its full row, and `story1_attdist_rung_b`'s existence lemma is
restated with its invariant hypothesis weakened to the two facts it reads (`esFG`). New
verdict packs are runner rows 42–46 (`Verdicts/RunModal.lean`), pinned in
`ModalPinTable`/`ModalTablePins`/`ModalCodePins`, and counted in `Coverage.expected.modal`
(483 → 522).

## 2c. Checked cuts — what the tool checks, and the five cut-composed theorems (2026-10-08)

**What a checked cut is.** For each mode (either side) the tool takes the mode's guard,
splits it into its non-strict conjuncts (`cutAtoms`: `≤`/`≥` atoms only), and keeps an atom
as a CUT when two obligations hold (`Trusted/OracleAPI.lean` `checkedCut`):

* **O1 (entry)** — the atom is implied by the mode's guard. Syntactic: every candidate *is*
  a guard conjunct, so a switch into the mode (guard-gated, the trust-base item) lands
  inside the atom.
* **O2 (invariance)** — the atom `g ≤ 0` is forward-invariant along THIS mode's own field,
  the other side frozen, λ irrelevant. Four routes, tried in order: `shape` (the atom is
  `v ≤ κ`/`v ≥ κ` and the field for `v` is a contraction `k(c − v)` with the equilibrium on
  the safe side — a rational comparison, no Z3; Lean `contract_stays`), `frozen` (every atom
  variable has field `0`; no Z3), `diStrict` (`UNSAT(evolve ∧ g = 0 ∧ ġ ≥ 0)`, the DI
  boundary query, route B) and `diNonstrict` (`UNSAT(evolve ∧ ġ > 0)`, whole-domain, route
  A). O2 is UNCONDITIONED — each atom over the bare evolve domain, no mutual narrowing — so
  the Lean lift composes per atom (`Proofs/Soundness/CutLift.lean`, `CutCover.lean`).

**How the cut narrows the flow query.** The kept atoms of the left mode `m_L` and the right
mode `m_R` are conjoined to the domain of every query of that pairing (`andCuts`): the joint
flow queries (`checkSeg`, all three routes), the static reposition regions (`repoRegions`)
and the dynamic reposition queries (`checkDynRepo`). `evolve` itself is never modified; the
model, and the Lean statement (uniform evolve as every mode's domain), see only `evolve`.
The emitted certificate is `Instances/EvolStrengthenings/<name>.lean` (atom + route per
mode), kernel-checked well-formed by `rfl` (`evolStrengtheningWF`: every atom is a guard
conjunct of its mode, shape/frozen tags re-checked by the pure recognizers), and the DI
atoms' O2 obligations are re-run by `--run-verdicts` (`Verdicts/RunCut.lean`: the **105 cut
probes**). Two sentences for Section 4.2: *a guard conjunct becomes a cut when the
certifier re-derives that the mode's guard implies it (entry) and that the mode's own
flow preserves it (invariance, by differential induction or a recognized contraction
shape); cuts are conjoined to the flow-query domains of that mode and never to the
model.*

**Which benchmarks use cuts.** 11 benchmarks carry a cut certificate with DI-route atoms
(the 11 cut-lifted `CutThroughout` instances; `RELCERT_NO_CUT=1` declines them; 13 before
the deduplication removed `arm_fidelity_high` and `plant_fan_high`, both identical to
`arm_chain_rung3`). The 97 probes, per benchmark (`docs/VERDICTS.md`, runner output,
"cut instances"):

| benchmark | probes | atoms (side/mode: route) |
|---|---|---|
| `arm_chain_rung3` | 4 | `R/ApproachA θ ≥ 0`, `R/ApproachB θ ≥ 0.35`, `R/ApproachC θ ≥ 0.5` (B strict); `R/Hold θ ≥ 0.6` (frozen, probed as A) |
| `refinement_ladder_rover_rung1_2to3` | 9 | `L/STEEP, MODER, FLAT` (A); `R/STEEP, MODER, FLAT` (A and C each) |
| `refinement_ladder_rover_rung3_6to8` | 12 | `L/…` (A and C each); `R/…` (A and C each) |
| `refinement_ladder_rover_rung4_8to12` | 9 | as `rung1_2to3` |
| `rover_attitude_cone_12dof` | 9 | as `rung1_2to3` |
| `rover_dof_terrain_rung1` | 9 | as `rung1_2to3` |
| `rover_dof_terrain_rung2` | 9 | as `rung1_2to3` |
| `rover_dof_terrain_rung3_8d` | 9 | as `rung1_2to3` |
| `rover_dof_terrain_rung3` | 9 | as `rung1_2to3` |
| `story3_rollover_base_12dof` | 9 | as `rung1_2to3` |
| `story3_rollover_ladder_rung_a` | 9 | as `rung1_2to3` |

`arm_fidelity_mid` also carries a cut certificate (`R/ApproachFast θ ≥
0`, `R/ApproachSlow θ ≥ 0.35`, B strict; `R/Hold θ ≥ 0.6`, shape) but is not cut-reliant
for the tool (it certifies without cuts at λ = 9/2, `Instances/BenchCoversNC/`; so did
the removed `plant_fan_mid`, at λ = 15/4) and is not probed: its Lean instance at λ = 1
uses the `Hold` region in the modal pack instead.

**The cut-composed theorems.** For `arm_chain_rung3` and `arm_fidelity_mid` (and, before
the deduplication, their duplicates `arm_fidelity_high`, `plant_fan_high`,
`plant_fan_mid`) the base modal theorems carry the
`Hold` cut `θ_R ≥ 0.6` as an invariant conjunct at EVERY right mode (`README.md`,
*Conditioning*). The declared invariant with plain `mvValid` is false (at `mv = Hold`,
`θ_R < 0.6` the right cannot respond — countermodel in `docs/CUT-COMPOSITION.md` §3). The
statement that composes the two cut obligations is the declared invariant with the cut
carried as **`Hold`'s mode region only**:

| paper element | Lean (`Instances/<Name>Declared.lean`) |
|---|---|
| `φ_declared` | `canonInvM gA []` — the file's row, nothing added |
| the cut at `Hold`: O1 entry ∧ O2 invariance | `mvRegionR mvA regionsA k` with `regionsA Hold = ⌊θ_R ≥ 0.6⌋`, `regionsA q = ⊤` otherwise (`EnvelopeChainR.lean`): at the approach modes this IS `mvValid`; at `Hold` it is the cut, established at entry (guard-gated switching) and kept by `Hold`'s flow (O2: `frozen`, resp. `shape`) |
| the right-only repositioning (`checkDynRepo`, route A, left frozen) | `sem_rightBlock_rate` (`Proofs/Encoding/CutComposition.lean`): the explicit constant-rate curve in the start mode to `θ_R = 0.6`, then zero-duration hops into `Hold` — Z3-free |
| the `Hold` phase | endpoint arithmetic `θ_L ≤ 0.65 ≤ 0.6 + tol` (the same fact that makes the base instances' route-B/C `Hold` queries unsat) |
| the conclusion | `rvalid (theorem3Form (bigChoice leftProgs) (rightAutomatonBody GrA mvA) (canonInvM gA [] ∧ envLR ∧ mvRegionR mvA regionsA k))` — `theorem <name>_declared`, axioms the standard three |

The per-benchmark table, the tool-run confirmation of the strategy and the countermodels
are in `docs/CUT-COMPOSITION.md`. The base theorems stand beside the new ones (50 theorems
in `ModalBattery` after the deduplication: 41 base, 7 mode-keyed, 2 cut-composed).

## 3. Full inventory of generic `rvalid (theorem3Form …)` theorems

Twenty-odd, in five families by what they assume. This variety is the "additional
machinery" — routes built at different times for different witness shapes.

**(a) Cover-based, Emit-free** — §2. The paper's Theorem 3 proper.

**(b) Settling / cadenced — ⚠️ VACUOUS for relational invariants. Do not cite.**
`theorem3_faithful_settling` (`Proofs/Soundness/GuardThreaded.lean:417`), its clocked and
cadenced variants (`Proofs/Encoding/ClockedTop.lean:41,368,462`), and
`settling_end_to_end` (`Proofs/Encoding/FvDischarge.lean:632`) all require a hypothesis of
the `GBoxAll` shape (`GuardThreaded.lean:380`), whose own docstring reads:

> **QUARANTINED (defective shape — task H).** Relational `g`-preservation along right
> residences, stated LEFT-CONTEXT-FREE: for an `L`-mentioning `g` and a drain-type mode
> this is **unsatisfiable** (the left coordinates are unconstrained), so no certificate
> battery can discharge it. … **Do not build on this.**

Why it is unsatisfiable, concretely: `BoxLe α g ν := ∀ ω, sem α ν ω → g ω ≤ 0`
(`dL-lean/DLLean/DI.lean:46`) is *unconditional* — the zero-duration run forces
`g ν ≤ 0` for **every** `ν` satisfying `Gd q`. But `Gd q` (`realGdOf`) constrains only
right-side coordinates, while a relational `g` mentions left ones. For watertank,
`g = x_L − x_R − 3`: take `x_R = 5` (inside Low's guard) and `x_L = 100`; then
`g ν = 92 > 0` and `BoxLe` fails. So the hypothesis is false and every theorem above is
**vacuously true** for the suite's actual relational invariants.

This is why R7 deprecated the cadenced chain and quarantined `GBoxAll`, and why the
S-arc built the replacement: *"the paper-faithful replacement couples each within-window
piece by its own JOINT certificate and each seam by a REPOSITION certificate
(left-contextualized)"*.

**What the settling battery does prove, non-vacuously:** the 46 `*_real` theorems
conclude `GuardSettlingB`, which mentions no invariant term at all — it says the right
system's flow exists for the control interval, stays in its evolution domain, and lands
in a state satisfying some retained successor's guard. That is the paper's
**well-formedness assumption** (nonblocking + successor-complete), discharged for 46/46.
Valuable, and worth claiming — but it is *not* relational invariant preservation.

**(c) `hstep`-parametric** (Emit-free by construction; `hstep` supplied per instance).
`theorem3_faithful` (`BridgeFinish.lean:77`), `theorem3_faithful_multi`
(`RepositionFinish.lean:27`), `theorem3_faithful_multiE` / `_multiE_LR`
(`EnvelopeChain.lean:170,387`), and the landing family
(`Proofs/Flow/MultisegLandingBridge.lean`). Here `hstep` is *literally* the paper's
eq. (relational-invariant): since `faModal ρ α β φ = [α]⟨ρβ⟩φ`, it reads "for every run
of one left body iteration there exists a run of the starred right automaton preserving
the invariant", and `relational_loop_multi` inside the proof is the paper's *"repeated
application … for every finite number of control cycles"*.

**(d) Emit-carrying** — superseded by (a), retained.
`decideCovered_implies_theorem3_faithful_multi` (`RepositionEndToEnd.lean:28`),
`theorem3_faithful_multi_reposition` (`:71`), `theorem3_uniform_multiflow`
(`UniformMultiflow.lean:300`), `uniform_multiflow_end_to_end`
(`UniformFvDischarge.lean:287`), and the two `*_of_emit` forms.

**(e) Encoding layer.** `theorem3_encoded` / `rvalid_of_encoded_unsat`
(`Checker/Cover/Encoding.lean:36,57`) — Z3 unsat on the encoded negation ⟹ `rvalid`, via
dL-rel's **Theorem 2** (`RFormula.encoding_correct`: soundness *and* completeness of the
bi-state↔host encoding, with `exists_bridge` proving it never vacuous).


### 3f. Findings from the full read of `Proofs/Encoding` (27 files, 7,746 lines)

**The Z3 leaf is exactly one theorem.** `segPres_from_flowCert`
(`BridgeDischarge.lean`) is the only theorem in the layer whose hypothesis is a
`z3solve … = unsat`; it produces `SegPreservesOn`. Every route above is parametric in
`CoverCert`, so `z3_unsat_sound` enters only there. This matches the axiom audit exactly.

**Route classification by hypothesis** (read off every signature in the directory):

| route | distinguishing hypotheses | verdict |
|---|---|---|
| cover / uniform — `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered`, `theorem3_uniform_guarded` | `cert : CoverCert`, `hchk : decideCovered`, `hproj : RightProjAlign(V)`, side-split disjointness | **live, non-vacuous** |
| settling / cadenced — `theorem3_faithful_settling`, `_clocked`, `_cadenced`, `_cadenced'`, `settling_end_to_end` | **`hgbox : GBoxAll`** (all four ClockedTop/GuardThreaded variants) or the same shape as `hcert` | **vacuous** (§3b) |
| Emit-carrying — `theorem3_faithful_multi_reposition`, `decideCovered_implies_theorem3_faithful_multi`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end` | `hemit : EmitSegs` / `EmitWindows` | assumes the witness; superseded by R1 |
| `hstep`-parametric — `theorem3_faithful`, `_multi`, `_multiE`, `_multiE_LR` | `hstep` plus disjointness only | sound; `hstep` supplied per instance |

**Three further defects, each already self-documented, each with a live replacement:**

1. `Hmulti_window_prefixed` (`EnvelopeChain.lean`) carries `hdisH`, which the file marks
   **UNSATISFIABLE for genuine hops** — "the frozen hop binds every left coordinate".
   The replacement `Hmulti_window1_prefixed` (k = 1) carries **no `hdisH`**, only
   `hcouple`; watertank's modal instance uses that one.
2. `ClockedTop`'s `hbudgetAll` is "unsatisfiable for autonomous benchmarks unless `domL`
   itself bounds time" — repaired in the uniform route, where "the clock caps every
   piece" (`UniformMultiflow.lean:10`).
3. `rightReach_is_R_real_run` (`JointBridge.lean`) requires **`NoRepoModes`** — it
   applies only to graphs with no reposition modes. A real scope limit on that
   particular reach→program bridge, not previously noted here.

**The disjointness side conditions are genuinely discharged, not hidden.**
`hdis_multi`, `hddF_multi`, `hddF_multiE` (`UniformFvDischarge`, `EnvelopeChain`) and
`hdis_aux`, `hddF_aux` (`FvDischarge`) prove them generically by side-splitting the
variable space into `Lv` / `Rv` / `Aux`. This is what makes the `Aux` placement of `mv`
and `tg` load-bearing — and it is the repair for the archived `MvFrozen` vacuity
(`BridgeUnit1.lean:119` records the same failure mode).


### 3g. Findings from the full read of `Proofs/Flow` (12 files, 5,165 lines)

**The trust leaf, counted exactly.** `z3_unsat_sound` is *applied* at **12 sites across 5
files**: `Trusted/Oracle.lean` (4 — flow certificate, segPreserves, and two pruning
wrappers), `Proofs/Soundness/CutLift.lean` (4 — the cut-channel routes),
`Proofs/Flow/BoxViability.lean` (1), `BoxViabilityBounded.lean` (1) and
`ViabilityWiring.lean` (2 — the face/anchor viability verdicts). Everywhere else the
`hz3 : z3solve … = unsat` occurrences are *hypotheses*, discharged by supplying named
facts. So the trust boundary is narrow and enumerable, but it is **not** confined to
`Trusted/` — the viability and cut routes apply the axiom directly. Worth stating
precisely rather than as "one leaf".

**`Instances/AxiomCheck.lean` prints only `flow_certified` and `segPres_from_flowCert`.**
The other leaf sites (cut lift, the four viability verdict theorems) are not in the
printed battery. Not unsound — they are the same axiom, used the same way — but the audit
under-reports the leaf set, and extending it would make the claim self-evident.

**Proven vacuity and proven satisfiability are used as a discipline, in both directions:**
- `SuccReachUnion_vacuous` (`MultisegLanding.lean`) takes **no hypotheses** and proves a
  tempting formulation unconditionally true — hence useless. The development uses the
  non-vacuous `SuccReach` instead. The vacuity is a *theorem*, not a comment.
- `WFBoundary_narrowing_satisfiable` and `narrowing_coherence_true` (`WFBoundary.lean`)
  go the other way: they exhibit witnesses proving the boundary hypothesis is
  satisfiable, so the instances built on it are not vacuous.

This is the pattern that makes the `GBoxAll` finding (§3b) legible rather than alarming:
where the project suspects vacuity it either proves it and retires the route, or proves
satisfiability and keeps it.

**The analytic core is real.** `PicardBridge.lean` (1,607 lines) carries genuine
Mathlib-level ODE work — `odeField_contDiff`, `odeField_lipschitzOnWith`,
`IsPicardLindelof` construction, `uniform_local_existence_on_compact`, compactness
subcovers, slab chaining. `StratifiedBarrier.lean` records that "mutual narrowing was
circular and unsound for the non-strict routes" and now routes through the repaired
indexed `stratified_barrier_sound`.

**Route-(b) existence cost, confirmed concretely.** `HExistSegB_of_viability`
(`ViabilityWiring.lean`) needs, per benchmark: `hM`, well-formedness, the face lists,
strict/growth bounds, domain satisfaction, `ha : 0 < a`, `hLipOn` and `hfbnd` (the
per-anchor Lipschitz and field-bound data). That is the S3 route-(b) price for
non-contract fields, and it is why watertank's contract route
(`hExistSegB_of_wellFormedFlowB`, 124-line file) was the cheap path.


### 3h. Findings from the full read of `Proofs/Transfer` (5 files, 3,918 lines)

This layer is the bridge from the **scaled integer model** — where the kernel
certificates live (values ×σᵢ, time in `dt`-units) — to the **real parsed benchmark**.
It is what makes the 40 `*_real` theorems mean something about the benchmark files.

- `Rescale.lean` (389 L) — `GuardSettlingB_rescale`, the scaling-transfer lemma, proved
  once: the scaled model's per-mode settling obligation implies the real one, provided
  the two sides correspond by the pushforward law `f(σ·x) = σᵢ·u·f'(x)` (exactly the
  coefficient laws `Faithful` checks) and guards/envelopes correspond under state
  scaling. The witness flow transports by `Φ'(t) = σ⁻¹·Φ(t/u)` (chain rule).
- `FaithfulBridge.lean` (2,307 L) — gives the kernel's raw `ℤ × ℤ` `QF` arithmetic a
  real denotation, so `Faithful`'s Boolean coefficient laws become real-valued
  pushforward identities. This is the bulk of the layer and it is genuine work.
- `FaithfulBridgeGuards.lean` (401 L) — terrain/affine guard-map variants.
- `FaithfulBridgePad.lean` (687 L) — the padded benchmarks (`vs.length < n`; eight before the deduplication, three after),
  where a padded coordinate needs an invertible scale the transcription does not supply
  (`sigmaPad`).
- `RealEndToEnd.lean` (134 L) — the generic per-family theorems; its header states the
  design intent plainly: *"Per-benchmark instantiation (Instances/) is then a dozen lines
  of `decide`/`rfl`/`norm_num` discharges — the watertank pattern, mechanized for all 46."*

**Non-vacuity of the 40 `*_real` theorems — checked, and it holds by construction.**
`GuardSettlingB` is `∀ base, sat (Gd q) base → …`, so it would be vacuous if
`realGdOf q` were unsatisfiable. `realGdOf` is a conjunction of per-coordinate closed
bands (`envFormulaR` ∧ the guard band). And `decideWellFormed` — kernel-checked `rfl`
for all 46 — includes `(List.finRange n).all fun i => bandOrdered (M.env i)`, where
`bandOrdered b` is `l ≤ h` when both endpoints are present, plus per-mode clauses
including `0 ≤ m.glo` and band-containment (`bandInside`). So band non-emptiness is part
of what every benchmark's well-formedness certificate establishes; the `*_real`
obligations are non-vacuous **because a kernel check says so**, not by inspection.
(Verified `bandOrdered` and the `decideWellFormed` clause list directly; did not trace
every `checkMode` sub-clause.)

**Net for §4:** the 40 `*_real` theorems are substantive — they establish, at the real
benchmark's own scale, that every declared right mode's flow exists for the control
interval, stays in its evolution domain, and lands in a state satisfying some retained
successor's guard. That is the paper's well-formedness assumption, discharged 40/40 and
non-vacuously.


### 3i. `Proofs/Soundness` (6 files, 2,397 lines) — and the consolidated route verdict

**`CutLift.lean` (505 L)** — the checked-cut channel. Four atom routes
(`atom_boxle_{R,L}_{nonstrict,strict}`) plus `AtomFact.ofLie`, each **conditional** on
the atom holding initially (`hinit`), so none repeats the `GBoxAll` trap. `cut_lift_boxle`
does the narrowing lift; `cut_hcert` assembles it from O1 (guard entry) and the Z3
verdict. Four of the twelve `z3_unsat_sound` sites live here.

**`CutChannel.lean` (70 L)** — the core lift, cleanly stated: if the invariant holds on
the narrowed domain `D ∧ S` and the flow provably stays in `S`, it holds on `D`.

**`UniformEvol.lean` (291 L)** — `contract_stays` and `WellFormedFlowB_contract` need
only arithmetic side conditions (`0 ≤ k`, band containment): **no Z3, no budget**. This
is why watertank's existence discharge (S3 route (a)) was cheap.

**A second documented vacuity trap: `hbudgetAll`.** It states that *every* solution of
the left ODE within `domL` has duration `≤ k·dt`. `ClockedTop.lean`'s header names it
outright: *"unsatisfiable for autonomous benchmarks unless the caller smuggles a clock
into `domL` — a vacuity trap"*. It is carried by `theorem3_faithful_settling` (which
therefore has **both** traps) and by the whole landing family —
`theorem3_faithful_landing_clocked`, `_wf`, and `_uniform`. Clocking the left retires it,
which is exactly what `ClockedTop` and the uniform route do.

**Consolidated verdict over every route to `rvalid (theorem3Form …)`:**

| route | distinguishing hypotheses | verdict |
|---|---|---|
| cover / uniform — `decideCovered_implies_theorem3_faithful`, `theorem3_uniform_from_covered`, `theorem3_uniform_guarded` | `CoverCert`, `decideCovered`, `RightProjAlign(V)` | **live** |
| `hstep`-parametric — `theorem3_faithful`, `_multi`, `_multiE`, `_multiE_LR` | `hstep` + disjointness | **live** |
| settling, unclocked — `theorem3_faithful_settling` | **`GBoxAll` and `hbudgetAll`** | doubly vacuous |
| settling, clocked/cadenced (×3) and `settling_end_to_end` | **`GBoxAll`** (budget retired by clocking) | vacuous |
| landing, clocked (×3 incl. `_uniform`) | **`hbudgetAll`** | vacuous for autonomous benchmarks |
| Emit-carrying — `*_of_emit`, `theorem3_uniform_multiflow`, `uniform_multiflow_end_to_end`, the reposition multi forms | `EmitSegs` / `EmitWindows` | sound, but assumes the witness — *unless discharged at the instance* |

**Both live instantiations survive this.** `rover_drag_multiflow` goes through
`uniform_multiflow_end_to_end`, whose `hcov` bundles `EmitWindows` — but the instance
**discharges it inside the proof**, leaving only `hz3` (one Z3 verdict) and `hES`
(existence). `watertank_modal` goes through `theorem3_faithful_multiE_LR` with `hstep`
assembled from six joint verdicts and six existence facts, the latter proven in-kernel by
`WatertankViability`. Neither touches `GBoxAll` or `hbudgetAll`.


### 3j. `Instances/` — the per-benchmark verdict, settled

Routing is uniform and was checked exhaustively, not sampled:

- **all 29** `Throughout/*.lean` apply `check_sound_multi` (33 before the deduplication);
- **all 11** `CutThroughout/*.lean` apply `check_sound_multi_cut` (13 before);
- **none of the 40** mentions `rvalid` — they stop at
  `Covered ∧ CoexecInvAllThroughout{,G}`.

Both are **live**: `check_sound_multi`'s certificate is `CoverCertM` over the *joint*
graph (`realModeOf` builds `jointSys` with domain `evolveL ∧ evolveR`) and its invariant
premise is conditional (`hinit : InvAllHolds gs ν`) — neither the `GBoxAll` nor the
`hbudgetAll` trap.

**The definitive per-benchmark table:**

| what is proven | benchmarks | route | status |
|---|---|---|---|
| relational invariant holds **throughout** every right co-execution | **40/40** (29 cut-free + 11 cut-lifted) | `check_sound_multi{,_cut}` from named Z3 verdicts | ✅ **live** |
| right-system well-formedness at the real scale — flow exists for the control interval, stays in its domain, lands in a retained successor's guard | **40/40** (`*_real`) | Transfer/rescale + `decideWellFormed` `rfl` | ✅ **live** (this is the paper's well-formedness *assumption*, discharged) |
| the instance **is** the parsed benchmark file | 40/40 | `faithfulSettling… = true := rfl` | ✅ live |
| the tool's cover decision, kernel-replayed | 40/40 | `coverReplays … := by decide` | ✅ live |
| full ∀∃ `rvalid (theorem3Form …)` | **40/40** (`Instances/ModalBattery.lean`; 41 base theorems — `rover3tier_rung12` has one per left mode — plus 7 mode-keyed and 2 cut-composed) | `theorem3_faithful_multi{E,F,R}_LR` | ✅ **live**; existence proven in every instance, 5 base instances Z3-free |
| `rvalid (theorem3Form …)` | `watertank` ×3 (`Archive/EndToEnd.lean`); `arm_refinement` (`Archive/Mega.lean`, deleted with the benchmark 2026-10-08) | settling route | ❌ **vacuous** (§3b) — archived 2026-07-30 |

**Answer to "are all benchmarks end-to-end verified?"** — depends on which statement:

- **Invariant preservation throughout co-executions: yes, all 40, non-vacuously**, from
  named Z3 verdicts with the instance pinned to the benchmark file by kernel `rfl` and
  the cover decision replayed by `decide`. This is the substantive relational result.
- **The ∀∃ modality (`theorem3Form`, the paper's Definition 1 / Theorem 3 conclusion):
  all 40 (46 before the deduplication), as of 2026-07-30.** Every certified benchmark has a non-vacuous instance in
  `Instances/ModalBattery.lean`; existence is proven in each (no `HExistSeg`-style
  hypothesis survives), and five instances carry no Z3 verdict at all. The old
  settling-route statements are vacuous as documented in §3b and now live in `Archive/`.
  How to check all of this: `docs/CERTIFICATION-CHECK.md`.


### 3k. What "Theorem 3 for all 46" took — the record

> **RESOLVED 2026-07-30.** This section was written when 2 of 46 were done, and it
> measured the obstacle correctly but predicted the wrong resolution. Kept because the
> measurement is still the clearest statement of what the shapes are; read the resolution
> note first.

The measured groups were: **9** benchmarks with every mode joint-certified (uniform
route, any k); **16** with a non-joint mode but budget 1 (the modal k = 1 route,
watertank's); **21** with both a non-joint mode and budget > 1 — the shape whose only
lemma, `Hmulti_window_prefixed`, carries a `hdisH` side condition its own note proves
unsatisfiable for genuine hops.

**How it actually resolved.** Not by repairing `hdisH`, and not by the fixpoint
reformulation:

* the 21 went through `Proofs/Encoding/RepoPrefixR.lean`, where the response prefix is a
  *right-only* hop program whose disjointness is **derived** rather than assumed, plus
  `WindowRF.lean` for the list-invariant variant — so the false side condition simply
  never arises;
* λ ≠ 1 windows state at the real automaton via `Reparam.lean`;
* multi-component invariants go through `EnvelopeChainM.lean`, mode-region ones through
  `EnvelopeChainR.lean`;
* the five intra-window mode-switching benchmarks go through `SplitCoupling.lean`
  (with an explicit `dt ≤ 1/5` cap in their statements);
* the last six — `rover3tier_rung12` and the five pump-hold/reposition-reliant ones —
  needed no new joint machinery at all. `rover3tier_rung12` is stated per left mode
  (its modes' invariants have genuinely different shapes). The other five use the
  **catch-up** form: because `faModal`'s `⟨…⟩` runs *after* the left window, the response
  may be a pure right-side flow, with the invariant re-established by endpoint arithmetic
  over `WindowGrowth.lean`'s displacement bound. Those five carry **no Z3 verdicts**.

**Interaction with the shelved fixpoint design.** `docs/proposals/FIXPOINT-DESIGN.md` §4 claimed the
winning-region reformulation would dissolve this blocker. It was never needed: the blocker
dissolved through the response-structure layers above. The design remains a recorded
alternative, not a dependency.

### 3l. The existence bridge that may already be paid for

`HExistSegB` (bounded) and `GuardSettlingB` (the `*_real` battery, 46/46) assert the
**same object**: a right flow from a start point, with `rightBlock fR lam` derivatives,
masking non-bound coordinates, staying in `domR`. Three differences, all small: the start
point (`ΦL s` vs `base` — reducible to `sat (Gd q) ν` since `Gd q` is right-only and the
left flow moves only left coordinates); the duration (restrict `[0,dt]` to `[0,s]`,
`ODESol_restrict` exists); and `GuardSettlingB` supplies an *extra* successor-guard
conjunct that `HExistSegB` does not need. `HExistSegB`'s own docstring records the design
intent — *"unlike the `∀s` `HExistSeg`, it is dischargeable from the HONEST bounded-`dt`
domain-invariance"*.

If that bridge lands, the **existence** half of the ∀∃ surcharge is already paid 46/46 by
a battery that currently feeds only vacuous routes (§3b), and the modal route's
per-benchmark existence cost drops to near zero. Note `GuardSettlingB` is indexed by right
mode only while `ESW` is per (left, right) pair, so |Q| facts should cover |L|×|Q|
obligations. **Not built** — the risk is matching the lowered data (`realFieldOf` /
`realEnvOf` against an instance's `fR` / `domR`).

---

## 4. What each benchmark has

**Ingredients, all 40 — kernel-checked:**

| artefact | file | check |
|---|---|---|
| the instance **is** the parsed benchmark file | `Instances/FaithfulCerts.lean` | 40 × `faithful… = true := rfl` |
| the tool's cover decision, replayed | `Instances/BenchCoverReplay.lean` | 40 × `coverReplays IR cover = true := by decide`, for **every** emitted left-mode cover and **every** admissible start |
| model well-formedness | `SettlingInstances` (19), `TerrainInstances` (19), `AffineInstances` (2) | `decideWellFormed … = true` by `rfl` |
| real-chart transport | `Instances/RealInstances.lean` | 40 `*_real` theorems — the generic family theorem instantiated at the parser-emitted IR, concluding `GuardSettlingB` |
| emitted data | `BenchIR/`, `BenchCovers/`, `BenchCoversNC/`, `EvolStrengthenings/`, `BenchViability2` | drift-checked literals |

**Per-benchmark theorem instantiations:**

| family | benchmarks | conclusion |
|---|---|---|
| `Instances/Throughout/*.lean` | 29 | `Covered … ∧ CoexecInvAllThroughout …`, per left mode, from named Z3 verdicts |
| `Instances/CutThroughout/*.lean` | 11 | same, guard-threaded via `RightReachG` |
| `Instances/*Modal.lean` (40 files) | **40** | **`rvalid (theorem3Form …)`** — 41 base theorems (+ 7 `*Handoff.lean` mode-keyed, + 2 `*Declared.lean` cut-composed), all imported and axiom-audited by `Instances/ModalBattery.lean` |
| `Archive/EndToEnd.lean` | watertank | `rvalid (theorem3Form …)` ×3 — **via the settling route, hence vacuous (§3b)**; archived 2026-07-30 |
| `Archive/Mega.lean` | arm_refinement | fidelity ∧ settling in one term — **same settling route, same vacuity (§3b)**; archived 2026-07-30, **deleted 2026-10-08** with the `arm_refinement` benchmark (a duplicate of `arm_fidelity_low`) |
| `Instances/UniformPilot.lean` | rover_drag | **`rvalid (theorem3Form …)`** from **one** Z3 verdict + `hES`; kept as the only instantiation of `theorem3_uniform_multiflow` (the benchmark's live instance is `RoverDragModal.lean`) |
| `Instances/WatertankModal` + `WatertankViability` | watertank | **`rvalid (theorem3Form …)`**, multi-mode with repositions, existence proven in-kernel; the six verdicts are pinned to the runner's printed queries |

So `rvalid (theorem3Form …)` is written out for **all 40 certified benchmarks**
(`Instances/ModalBattery.lean`), non-vacuously: each instance carries a joint certificate
or a right-only response, existence is proven rather than hypothesised, and five carry no
Z3 verdict at all. The `EndToEnd` form remains vacuous (§3b) and is archived (`Mega` was deleted with its benchmark).

**Historical note — why an earlier version of this section said the remaining 43 were far
off.** That analysis was correct about the *uniform* chain: the throughout battery builds
`CoverCertM` (multi-component), the uniform `rvalid` route wanted `CoverCert` (single `g`)
plus `RightProjAlignV`, and no bridge between them existed. The gap was closed by not
using that route at all. `EnvelopeChainM.lean` states the modal chain over a **list** of
invariant components directly (`theorem3_faithful_multiF_LR`), so no `CoverCertM →
CoverCert` bridge is needed; `EnvelopeChainR.lean` adds the mode-region variant; and the
`hstep` assembly is discharged per benchmark from the emitted cover rather than from
`RightProjAlignV`. The two chains are still disconnected — the throughout battery and the
modal battery are independent statements over the same emitted certificates — but the
modal side no longer needs anything from the uniform side.

---

## 5. Where the real distinctions lie

Not coverage — **witness shape**:

| | cadenced / settling | uniform window chain | multiflow + repositions |
|---|---|---|---|
| generic theorem | (b) | (a) | (c) + (d) |
| written out at | watertank, arm_refinement | rover_drag | watertank |
| witness | one right cycle per round, full width | window chain over declared self-edges | several right cycles, mode changes, right-only reposition segments |
| paper content | Definition 1 / eq. (mode-inv) | + window chaining | + **§4** (all-successors cover, budget, repositions) |
| status | R7: cadenced chain **RETIRED** — parity reached 2026-07-30 (modal form on 46/46, cut lift on 13/13); the settling/cadenced files are in `Archive/` | — | current |

**Modelling choices to state in the paper** (all documented in-repo; none are defects):

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `mv`, clock | left flattened to `star (bigChoice leftProgs)`, guard-free — or guard-gated in `theorem3_uniform_guarded` | **stronger**: the left is ∀-quantified, so over-approximating strengthens |
| `?guard_m(x)` on transitions | `e.guard = ⊤` | permissive — the documented "⊤-model"; harmless because the cover is demonic over successors (`docs/COVER-AUDIT.md`) |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` | clocked in the cadenced/landing routes; unclocked in `rightAutomatonBody` | permissive where unclocked |
| invariant `φInv` | `φInv ∧ mvValidR` (and `∧ envLR` in the E-forms) | bookkeeping conjuncts, both sides of the implication |
| jump-then-flow | flow-then-jump | rotation (`docs/proposals/ROTATION-SCOPE.md`) |
| budgets `B = ε_L`, `w = ε_R/λ` (real-valued) | `weight : ℕ`, budget `⌈ε_L/δ_L⌉` | faithful ℕ-discretization |

**Two paper assumptions land well.** § Well-formedness (nonblocking + successor
completeness) is exactly what `GuardSettlingB`'s final conjunct **proves** for all 46; and
Limitations already says resets are identities, matching the mechanization
(`docs/proposals/RESET-MAPS-SCOPE.md`). **Definition 4** (All-Successors Cover) maps onto
`Covered`/`decideCovered` — base case `B ≤ w`, successor case ∃kind ∀retained-edges,
σ ↔ `SrcSetting`.

---

## 6. The R-series gates, and what each supports in the paper

The development was built as an ordered arc (`docs/history/ROADMAP.md`), R1–R7, each item
carrying an **acceptance gate** — the concrete artifact that counts as done: *"an item is
done when its gate is kernel-green, committed, and pushed."* The gates are the natural
evidence list for a referee, because each removes a specific way the mechanization could
have been weaker than the paper.

| item | what it removed / established | gate | Lean artifact | paper element it supports |
|---|---|---|---|---|
| **R1** witness extraction | the assumed `EmitSegs`/`EmitWindows` devices — hypotheses asserting *a chain of response segments exists*. Replaced by induction on the `Covered` derivation (joint cases → pieces; the four reposition cases → frozen-left segments; staying backed by declared self-edges) | *"`theorem3_faithful_multi{,_reposition}` restated without any `Emit*` hypothesis; rover_drag pilot re-based on it; axioms unchanged"* | `theorem3_uniform_from_covered` (`CoverExtract.lean:122`) | **Theorem 3** and **Definition 5 (Witness Strategy)** — makes "the cover *induces* a certified witness strategy" an inference rather than an assumption. Without R1 the mechanization would assume exactly what §4 constructs |
| **R2** statement conditioning | quantification over more initial configurations than the tool certifies (instances demanded "phantom pairs"). Entry conditioned on `admissible` (SAT `guardL ∧ guardR ∧ inv`), `mv = q₀`, `σ = preJ`; left family = all modes' windows, each `test(guardL)`-gated | *"top theorem's start set provably matches `coverMode`'s admissible-start ∀; a watertank-shaped 3-mode toy goes through where it previously demanded phantom pairs"* | `theorem3_uniform_guarded` (`CoverExtract.lean:218`) | **§4.3 admissibility** (*"an initial right mode is admissible for `m_L` if some initial state pair satisfies `φInv`"*) and **eq. (mode-inv)**'s per-mode, guard-entered decomposition |
| **R3** canonical `ϕinv` + encoding identity | the per-instance `hψ`/`hinvL`/`hinvR` residuals — a builder from the lowered invariant components plus a generic `encode … = invLe g` proof | *"pilot instance carries NO encoding hypotheses"* | `canonInv`, `encode_canonInv` | **eq. (polynomial-invariant)** — the invariant language `⋀ᵢ p_i ≤ 0` — and the encoding step into dL-rel's Theorem 2 |
| **R4** multi-component invariants | certification of only the primary component. Per-component certificates via three routes (A domain / B strict / C superlevel), each component's domain narrowed by the others `≤ 0` (multi-barrier coupling) and by the checked cuts | *"a multi-component benchmark's full conjunction invariant certified, not just the primary component"* | route adapters + the multi-barrier lemma; `CoverCertM` | **Definition 2 (Flow Certificate)** and **Theorem 1** — the paper's *"when this condition holds for every component, no boundary of the conjunction can be crossed outward"* |
| **R5** emission door + battery | hand-built instance data. `--emit-cover` emits λ, budget, node flags, edges + pruned bits, admissible starts and the verdict list as drift-checked literals; the generator writes instances re-running `decideCovered` in the kernel | *"all 46 tool-certified benchmarks build with axioms exactly `[propext, Classical.choice, Quot.sound, z3_unsat_sound]`; suite + drift + trust audits green"* | `Instances/BenchCovers/`, `BenchCoverReplay.lean` (46 × `by decide`) | the **evaluation claim** (§5) — that what the tool reports CERTIFIED is what the kernel checks, per benchmark |
| **R6** viability certificates | the last analytic hypothesis: that certified evolutions exist for the needed durations. Per mode, per evolve-box face, `UNSAT(on-face ∧ field-outward)`, plus one generic Picard lemma | *"viability hypotheses removed on every mode whose face-queries pass; legitimate failures fall back to a named per-mode hypothesis or a model-margin fix"* | `Proofs/Flow/BoxViability*`, the face census (1121/1121) | the **existence side of Definition 5** — a witness strategy must map to an actual execution, not merely a formal segment chain. Also the counterpart to the paper's "bounded-time reachability" paragraph |
| **R7** closure | drift between the docs' stated assumptions and the proofs'. Cadenced chain deprecated, contract frozen | *"`#print axioms` battery = the four axioms everywhere; hypothesis list in docs matches the frozen contract verbatim"* | `Instances/AxiomCheck.lean` | the **trust-base claim** — what a paper section on the mechanization would assert about its assumptions |

**The follow-on S-arc**, for completeness: **S1** built the reposition-window modal form
(multi-mode `rvalid`) — the paper's §4 multi-step matching; **S2** the guard-threaded cut
lift for the 13 cut-reliant benchmarks — the paper's use of guards to strengthen the
evolution constraint (§3); **S3** bounded-time viability wired per mode — existence;
**S4** housekeeping.

**How to use this list in the paper.** R1 and R2 are the two a referee should care about
most: R1 is why the mechanized Theorem 3 does not assume its own conclusion, and R2 is
why its ∀ ranges over exactly the admissible entries the tool certifies rather than a
larger phantom set. R5 is why "certifies all 46" is a kernel-checked claim rather than a
tool report. R4 and R6 are why the certificate covers the *full* conjunction invariant
and a *real* execution respectively.

---

## 7. Record: how the earlier assessments went wrong

Three prior versions of this file understated the development. The causes, so they are
not repeated:

1. **Searching for a name instead of reading.** R1's deliverable was looked up as
   `emit_from_covered` (the task-list name); not finding it, the assessment concluded the
   work was missing. It had shipped as **`theorem3_uniform_from_covered`**.
2. **Reading one sibling and generalizing.** Seeing `theorem3_faithful_multi_of_emit` led
   to "the chain is Emit-bound", without checking for the Emit-free sibling defined
   earlier in the same file.
3. **Anchoring on one route.** The modal/multiflow route was treated as the only path to
   `theorem3Form`, so the settling, uniform, and cover-based routes were never surveyed.
4. **Correcting by spot-check.** Each revision fixed one symptom from another partial
   read rather than enumerating the top theorems once.

The enumeration in §3 exists so that any future claim about "what is missing" is checked
against a list rather than re-derived.

---

## 8. Note on `tooling_sound`

`Archive/GapThreeTask3.lean:63` is the Arc-1 automaton-parametric statement — programs
derived from two `HybridAut`s via `graphOf_Gr` — instantiated non-vacuously at rover data
(`GapThreeRoverTooling.lean:531`). It routes through `EmitSegs`, so it is superseded by
§2's cover-based, Emit-free theorems. Its one surviving contribution is packaging:
deriving the programs from an automaton rather than taking `leftProgs`/`G` as given,
which is worth borrowing only if an automaton-parametric statement is ever wanted.

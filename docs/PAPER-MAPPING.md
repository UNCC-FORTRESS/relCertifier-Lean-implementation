# Paper ↔ mechanization: the map

Read this with the paper open. One section per formal element of the paper, in the paper's
order; each says what the Lean name is, where it lives, how its hypotheses are discharged, and
which axioms it rests on. Paper references are to *Certifying Forall-Exists Invariants for
Cyber-Physical Systems via Witness Construction*, the HSCC+ICCPS 2027 submission, in the
submission's numbering, Appendices A to C included (§10 maps the appendices). The repository
layout is in `README.md`; the build and check recipe, with every expected count, is
`docs/CERTIFICATION-CHECK.md`. Paths below are relative to `RelCertifier/` unless they start
with `docs/`, `scripts/` or `benchmarks/`.

**The numbering, verified against the submission's `paper.aux`.**

| paper | label | section |
|---|---|---|
| Definition 1 (∀∃ Relational Invariance) | `def:forall-exists` | 2.3 |
| Definition 2 (Mode Fact) | `def:checked-cut` | 3 |
| Definition 3 (Segments) | `def:segments` | 3 |
| Definition 4 (Witness Strategy) | `def:strategy` | 3 |
| Definition 5 (Flow Certificate) | `def:flow-certificate` | 4.1 |
| Definition 6 (Non-Connection Certificate) | `def:non-connection-certificate` | 4.2 |
| Definition 7 (Reposition Certificate) | `def:progress-certificate` | 4.3 |
| Definition 8 (Cover) | `def:response-cover` | 5 |
| Assumption 1 (Well-Formedness) | `asm:well-formed` | 3 |
| Lemma 1 (Time Stretching) | `lem:stretching` | 4.1 |
| Lemma 2 (Lie Conditions) | `thm:flow-sound` | 4.1 |
| Lemma 3 (Proving Joint Segments) | `lem:joint-segment` | 4.2 |
| Lemma 4 (Proving Right-Only Segments) | `lem:rightonly-segment` | 4.3 |
| Lemma 5 (Covers Are Witness Strategies) | `lem:cover-strategy` | 5 |
| Lemma 6 (the claim at a node), inside the proof of Theorem 1 | `app:lem-node-claim` | A.5 |
| Theorem 1 (Soundness of Witness Strategies) | `lem:composition` | 3 |
| Theorem 2 (Composition) | `thm:composition` | 3 |
| Theorem 3 (Soundness of Synthesis) | `thm:global-soundness` | 5 |
| Eq. 1, the model (modes with dynamics, evolve domain, guards, `next`, a clock) | `eq:model-timed` | 2.1 |
| Eq. 3, the relational property | `eq:relational-property` | 2.2 |
| Eq. 4, the water tank's ∀∃ property | `eq:tank-forall-exists` | 2.2 |
| Eq. 6, the relational invariant (one iteration) | `eq:relational-invariant` | 2.3 |
| Eq. 7, the per-mode obligation | `eq:mode-inv` | 2.3 |
| Eq. 8, the polynomial invariant | `eq:polynomial-invariant` | 2.3 |
| Eq. 9, the mode-dependent invariant | `eq:mode-dependent-inv-global` | 2.3 |
| Eq. 10, the strengthening `str(φ) → [\|(L*,R*)⟩⟩ str(φ)`, `str(φ) ≡ φ ∧ op_R ∧ Q_{u_l} ∧ Q_{u_r}` | `eq:strengthening` | 2.3 |
| Eq. 12, the per-mode `str` obligation | `eq:mode-str` | 3 |
| Eq. 13, the handoff condition | `eq:handoff` | 3 |
| Eq. 14, the joint product program | `eq:joint-dynamic-stretched` | 4.1 |
| Eq. 15, the right-only product program | `eq:rightonly-product` | 4.1 |
| Eq. 16, the Lie derivative condition | `eq:lie-condition` | 4.1 |
| Eq. 17, the boundary form | `eq:boundary-preservation` | 4.1 |
| Eq. 18, the domain form | `eq:domain-preservation` | 4.1 |
| Table 1, the suite by application area | `tab:benchmarks` | 6.3 |
| Table 2, the refinement ladders | `tab:ladder` | 6.4 |
| Table 3, the per-benchmark results | `tab:per-benchmark` | Appendix C |

Eqs. 2, 5 and 11 are unlabelled displays (the water tank's mode program, the running
example's ∀∃ invariance, and its `str`).

**Vocabulary: the paper's terms and the tool's names.** The tool and the Lean development
keep their own names; this table is the map, and the sections below use the paper's term with
the tool's name in parentheses at first use.

| paper | tool / Lean |
|---|---|
| mode fact `I_m` of a mode (Definition 2), found in preprocessing | the checked cut of the mode, its conjuncts the kept atoms: `OracleAPI.checkedCut` / `checkedCutX`, `EvolStrengtheningX` (`InstancesV2/Cuts/<b>.lean`), the `cuts` of `regionG guard cuts`, `cutsOK`, the stay verdicts, `CutLiftX` |
| joint segment, right-only segment (Definition 3), over one pair of modes | the certificate side: a joint segment's flow fact is a pack `modalVerdX` at the pairing's stretch, a right-only segment's is a reposition pack `modalVerdDynX` plus a progress certificate; the tool's "windows" are the left side's clock-capped cycles (`window_t`, `gwindowSeg`), one per left mode, which the segments of one strategy branch fill |
| entry states of a segment | the anchor `A l q` (`Proofs/Encoding/Emitted/Anchor.lean`) |
| witness strategy (Definition 4), the tree | the cover: `CoveredX` (`Checker/CoverX.lean`), the emitted record `CoverEmitE`, its walk `coverX_piece` |
| stretch `λ ≥ 0` (Lemma 1, Definition 5); stretch 0 = the witness stands still on a joint segment | `lam l q` per pairing, `lamQ` per window, `lamN`/`lamD` in the records (the bridge instance replays the stretch of every pairing from the emitted cover); stretch 0 is the tool's "stutter" (`docs/STUTTER.md`), a candidate only when the declared range includes 0 (`lambda_min = 0`) |
| flow certificate `flowC` (Definition 5) | a pack discharged by one of the three routes (A whole-domain, B boundary, C superlevel); `hbox`, `couple_box_cutX`, `couple_box_dyn` |
| non-connection certificate (Definition 6); pruning a declared mode change | pruning: `NonConn.queries` (source and barrier checks), `nonconn_sound`, the `pruned` list of the cover, `SearchGraph.retainedSucc`; `RELCERT_NO_PRUNE=1` disables it |
| reposition certificate (Definition 7), its stage list and landing target | the progress certificate: `Trusted/ProgressEmit.lean` (stages, rate / keep / land queries), `RepoProgress`, `repoProgress_*`, `progressVerd_*`, `relcert-progress-verdicts`; `RELCERT_NO_PROGRESS=1` disables it |
| restricted mode `m_R \| ¬landing target` (right-only certificates checked before landing only) | the pre-landing region: `Trusted/PrelandEmit.lean`, the record `PrelandEmitE` (`InstancesV2/BenchPrelanding/<b>.lean`), `plOK`, `withPL`, the `repoProgress_*_reg` lemmas, `theorem3_window_of_records_pl` / `theorem3_keyed_of_records_pl` (`docs/PRELANDING.md`) |
| retained successors `ret(q)` | `SearchGraph.retainedSucc`: declared, non-self, not pruned |
| landing set `S` of a segment (the children of a strategy node) | the retained successors for the all-successors rules (`step`, `stepRepoPre/Post`), or the chosen set `S` of `stepChosen` / `repoChosen` |
| committed successor subset (Lemmas 3 and 4, Definition 8) | the existential mode choice ("choice"): `stepChosen`, `repoChosen` and the entry hop `hop`, their coverage certificates `hcovJ` / `hcovR` / `hcovS`, `Trusted/ChoiceEmit.lean`, the choice groups of `relcert-bridge-verdicts`; `RELCERT_NO_CHOICE=1` disables it |
| operating region `op_R` (the right can select a successor of its stored mode) | the mode-consistent region `regionG guard cuts q = guard q ∧ cuts q` of the right's current mode, carried in the loop invariant as `mvRegionR` |
| cover of a configuration `(m_R, B, σ)` (Definition 8) | `Config = ⟨q, B, SrcSetting⟩`, `decideCoveredX` (fuel-bounded), the budget `B = ⌈ε_L/δ⌉` |
| handoff condition (Eq. 13) | `Handoff.queryOf`, the hypothesis `hhand` of `theorem3_modeKeyed` |
| Assumption 1 (Well-Formedness) | `WellFormedR` / `WellFormedRIn`, one proof per benchmark (`InstancesV2/WellFormed/<B>.lean`) |
| Theorem 3 (Soundness of Synthesis) | "Theorem 3" in every Lean docstring and in this file; `theorem3Form`, `theorem3_of_coverX`, `<b>_bridge` |

**Lean names.** The Lean names keep the development's vocabulary; the comments and
docstrings use the paper's numbering. `theorem3Form`, `theorem3_of_coverX` and the
`<b>_bridge` instances are the paper's Theorem 3; in this file "a benchmark's Theorem 3" or "a
Theorem 3 instance" names that Lean statement. The reposition certificate (Definition 7) is
the "progress certificate" (`ProgressEmit.lean`, `repoProgress_*`, `progressVerd_*`,
`RepoProgress`). The paper's `I_m` (a mode fact of mode `m`, Definition 2: one per mode, `true`
by default, fixed by preprocessing) is the tool's checked cut, whose conjuncts are the kept
atoms; the Lean names keep "cut" (`checkedCut`, `EvolStrengtheningX`, `CutLiftX`, the stay
verdicts). With no Lean statement of their own: Definition 3 (Segments), Definition 4
(Witness Strategy), Theorem 1 (Soundness of Witness Strategies), Lemma 3 (Joint Segments) and
Lemma 4 (Right-Only Segments). Theorem 1 is the cover induction `coverX_piece` and Lemmas 3
and 4 are steps of it (§2.2 below), as Appendix B.3 says.

**The claim, in one sentence.** For every benchmark of the suite, the paper's Theorem 3 at
the declared invariant (the Lean "Theorem 3") is a kernel-checked Lean theorem whose only
non-standard axiom is Z3's `unsat` (`z3_unsat_sound`), produced by one generic theorem
(`theorem3_of_coverX`) instantiated from the records the tool emits; and Assumption 1 of
every right model is a separate kernel theorem with no Z3 leaf.

## 0. The route to the statement

| theorem per benchmark | how the proof is produced | reference |
|---|---|---|
| `InstancesV2/Bridge/<B>.lean`, `<b>_bridge`: 52 instances, the 50 suite benchmarks (32 mode-independent through `theorem3_window_of_records`, 18 mode-keyed through `theorem3_keyed_of_records`, 41 of them through the `_pl` forms) and the 2 committed-subset exhibits of `benchmarks/choice/` | generated by `scripts/gen_bridge.py` from the emitted records; structural facts by `decide +kernel`, Assumption 1 transported from the benchmark's `WellFormedR` lemma and lifted by one coordinate (the right clock; instance dimension `bridgeDimV2 b` = the lemma's dimension + 1), every Z3 fact as one `Verdicts` hypothesis discharged by `relcert-bridge-verdicts` (13677 groups over the 52 instances) | `docs/BRIDGE.md`; axioms: standard three + `z3_unsat_sound` |

Five further bridge files (`InstancesV2/Bridge/{SaltTankStutter, EngineCoolingPrelanding,
StoplineFrictionMixed, HoldRepositionStrict, WatertankStrict}.lean`) instantiate the stretch-0
demo, the pre-landing demo, the mixed-direction progress demo and the two strict-invariant
exhibits (`docs/CERTIFICATION-CHECK.md`, check 5). An earlier route of hand-written standalone
instances is on branch `archive/legacy-2026-10`; its per-benchmark findings are kept in
`docs/GUARDED-SWITCHING.md`. The two `InstancesV2/Choice/General/` files (`VehicleAccelCopy`,
`WatertankChoice`) hold only the exhibits' right models and Assumption 1 proofs.

## 1. Section 2: the problem

| paper | Lean | where |
|---|---|---|
| the model (Eq. 1): modes with dynamics, evolve domain, guards, declared successors `next`, a clock | the parsed `PProblem` (`Trusted/Parse.lean`), one literal per benchmark (`InstancesV2/BenchIR/<b>.lean`, re-parsed and compared by `relcert-test`); the search graph `SearchGraph` of right modes and edges, the left automaton `LeftAut` | `Trusted/Parse.lean`, `Checker/Cover.lean`, `Proofs/Encoding/ModeHandoff.lean` |
| the two-system program `(L, R)` of the relational formulation: the left runs its guard-gated program, the right responds | `theorem3Form L R Φ = Φ → [|(L*, R*)⟩⟩ Φ` with `L = leftAutomatonBody A u_L` (jump then flow: `?(u_L = m') ; ⋃_{t ∈ next m'} ?guard_t ; u_L := t ; window_t`) and the clocked right automaton `rightAutomatonBodyC` (flow then jump, §9); the ∀∃ modality is dL-rel's (`faShape`), bridged by `RFormula.encoding_correct` | `Checker/Cover/Encoding.lean`, `Proofs/Encoding/ModeHandoff.lean`, `Proofs/Encoding/JointBridge.lean` |
| **Definition 1** (∀∃ relational invariance): `φInv → [|(L,R)⟩⟩ φInv` | `RFormula.rvalid (theorem3Form L R Ψ)`, the conclusion of every Theorem 3 instance | `Checker/Cover/Encoding.lean` |
| Eqs. 6 and 7: one iteration, per left mode | the per-window step `GResp` (one left window, the right's guarded response) and its assembly into the loop | `Proofs/Encoding/GuardedSwitch.lean`, `EnvelopeChainR.lean` |
| Eq. 8: `φInv` a conjunction of polynomial inequalities | `canonInvM g gs` (the list of components as one canonical formula; its encoding theorem `encode_canonInv`) | `Proofs/Encoding/CanonicalInv.lean`, `EnvelopeChainM.lean` |
| Eq. 9: `Φ = ⋀_m (u_L = m → φ_inv(m))` | `psiK u_L ϕ nL domL domR BkR`: the rows keyed by `u_L`, both envelopes, the right bookkeeping, `u_L ∈ modes` | `Proofs/Encoding/ModeHandoff.lean` |
| Eq. 10: `str(φ) → [|(L*,R*)⟩⟩ str(φ)`, `str(φ) ≡ φ ∧ op_R ∧ Q_{u_l} ∧ Q_{u_r}` | the loop invariant `φInv ∧ envLR domL domR ∧ mvRegionR mv (regionG guard cuts)`: `envLR` is `Q_{u_l} ∧ Q_{u_r}` with one domain per side, `mvRegionR` is `op_R` with the mode facts | `Proofs/Encoding/Emitted/Window.lean`, `Emitted/Keyed.lean` |

What the mechanized loop invariant carries beyond `φInv`: the evolve envelope `envLR` of both
sides and the right's mode-consistent region `regionG guard cuts q = guard q ∧ cuts q` (the
guard of the right's current mode and that mode's mode facts `I_m`; the paper's operating
region `op_R`), bookkeeping that the flow-then-jump rotation maintains at every loop boundary.

## 2. Section 3: mode facts, segments, witness strategies, Assumption 1, composition

| paper | Lean | where |
|---|---|---|
| the run-time reading of a witness strategy: for each left cycle a chain of right segments (joint, right-only, and switches), chosen after the left run | `GResp G q P post σ` (the segments are chosen after the left run; the final successor at the end state) and the chain lemmas `RResp`/`RRespP` | `Proofs/Encoding/GuardedSwitch.lean`, `GuardedClimb.lean` |
| the operating region `op_R` and the admissible initial modes | the right's mode-consistent region `regionG guard cuts q` (§1) and `AdmissibleStart` (§6.1) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Anchor.lean` |
| a right-only segment (the right moves alone, the left frozen) | the right-only steps of `CoveredX` (`stepRepoPre`, `stepRepoPost`), the frozen left in `couple_box_dyn` | `Checker/CoverX.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| every mode switch of the witness passes the entered mode's guard | `SwitchLegal e ω := Formula.sat e.guard ω`; a right run is a sequence of legal switches (`guarded_rights_bridge`); every edge of the instance's graph carries the lowered guard of the mode it enters (`grOf_guards`) | `Proofs/Encoding/GuardedSwitch.lean`, `Proofs/Encoding/Emitted/Data.lean` |
| **Definition 2** (Mode Fact), the preprocessing phase ("Preprocessing: mode facts."): a formula `I_m` over the variables of `m` is a mode fact of `m` if `g_m → I_m` and `I_m → [F_m] I_m` are valid; it then holds throughout every cycle of `m`. Preprocessing fixes one `I_m` per mode (`true` by default), and every obligation about a pairing `(m_l, m_r)` assumes `φ_inv(m_l)` together with `I_{m_l} ∧ I_{m_r}` | the tool's checked cut: per kept atom the entry check O1 (`g_m → I_m`) and the preservation check O2 (`I_m → [F_m] I_m`, by one of the three routes of §3), found by `OracleAPI.checkedCut` / `checkedCutX` (untrusted), recorded as `EvolStrengtheningX` (`InstancesV2/Cuts/<b>.lean`, well formed by `cutsOK_wfX`), O2 re-sent as the stay verdicts (`Bridge.stayQueryOf`, `atomsStayC_L/R`), and lifted to "holds along every run of the mode" by `Proofs/Soundness/CutLiftX.lean`; the kept atoms of both modes of a pairing are part of the anchor (§2.2), which is how the mode facts enter every obligation | `Trusted/OracleAPI.lean`, `Checker/EvolStrengthening.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean`, `Emitted/Stay.lean` |
| **Definition 3** (Segments): `seg^σ_joint(m_l, m_r, τ, S)` and `seg^σ_r-only(m_r, S)` in a source setting `σ`, from the entry states `entry(m_r) ∧ γ_σ` (`γ_pre-j = g_{m_l}`, `γ_post-j = true`) | no Lean definition of its own; the two segment obligations are what the joint and right-only cases of `coverX_piece` establish, §2.2 below; the setting is the `pre` flag of the configuration, and the pre-joint premise `γ_σ` is `(pre = true → Formula.sat gL y)` in `RepoProgress` | `Proofs/Encoding/CoverResp.lean` |
| **Definition 4** (Witness Strategy): a finite tree of right modes labelled with segments, rooted at an initial right mode `q₀` | the tree is the cover `CoveredX` walked by `coverX_piece`, §2.2 below | `Checker/CoverX.lean`, `Proofs/Encoding/CoverResp.lean` |
| **Assumption 1** (Well-Formedness), with the remark that `next(q)` always serves as the exits of a joint segment | `WellFormedR`, §2.1 below; adequacy of `next(q)` is clause (ii) | `Proofs/Encoding/WellFormedR.lean` |
| **Theorem 1** (Soundness of Witness Strategies): witness strategies for every admissible initial mode of a left mode give the per-mode obligation Eq. 12 (`str(φ_inv(m_l))` kept by one cycle of `m_l` against `R`) | the cover induction `coverX_piece` and its window assembly, §2.2 below; no standalone ∀∃ statement | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| **Theorem 2** (Composition): the per-mode strategies of Theorem 1 for every left mode, plus the handoff condition Eq. 13 at every declared left mode change, give the ∀∃ invariance within `op_R` and the stored modes' domains | `theorem3_modeKeyed_gen` (the clocked mode-keyed assembly with the conditioned handoff hypothesis; the unclocked `theorem3_modeKeyed` beneath it); the loop invariant `psiK` carries the envelope `envLR domL domR` from the start, and the first iteration performs a handoff | `Proofs/Encoding/ClockedKeyed.lean`, `Proofs/Encoding/ModeHandoff.lean` |

### 2.1 Assumption 1 (well-formedness)

| paper | Lean | where |
|---|---|---|
| **Assumption 1**: the right model is nonblocking and complete with respect to its declared successors: from every state in a source-mode guard an evolution spanning `ε_R` exists, and every evolution of duration at most `ε_R`, the empty one included, ends in the guard of a declared successor | `WellFormedR G guard ε`: for every mode `q` and state `x` in `q`'s lowered guard and evolve domain, (i) `∃ Φ, ODESol m.sys m.dom x ε Φ`, (ii) every run of duration `t ≤ ε` ends in `guard e.tgt` for some `e ∈ G.edgesFrom q` (the self-loop included); `G` the benchmark's guarded right automaton, `ε` the file's `epsilon` | `Proofs/Encoding/WellFormedR.lean` |
| its use in Theorem 3 | the hypothesis `hwf` of `theorem3_of_coverX`, `theorem3_keyed_of_records` and `theorem3_window_of_records`, stated as `WellFormedRIn G guard reg ε` (Assumption 1 relative to a region `reg` kept by the right flows; every instance takes `reg = ⊤`, the paper's form) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Region.lean` |
| proved, not assumed, per benchmark (Appendix B.5) | `<ns>.<b>_wellFormedR` for all 50 right models, Z3-free, audited on every build by `InstancesV2/WellFormedBattery.lean` (78 axiom lines: 76 at the three standard axioms, for the 50 theorems and the lemmas they share, and 2 for the `CutLiftX` lift, which add `z3_unsat_sound`); transported onto the bridge's graph by `wellFormedR_transport`, or stated over that graph directly (`<b>_wellFormedR_direct`, the 10 literature benchmarks); then lifted by one coordinate, from the lemma's dimension `n0` to the bridge dimension `n0 + 1` (the right clock), by `wellFormedR_lift` under the kernel-decided bundle `padOK IR n0` (every right guard and evolve domain lowers at `n0 + 1` to the embedding of its lowering at `n0`, and the dynamics pad with the new coordinate frozen) | `InstancesV2/WellFormed/`, `Emitted/Transport.lean`, `Emitted/Lift.lean`; `docs/WELLFORMED.md` §6 |
| the remark (self-loop whose guard contains the one-interval reach set, or a successor covering the rest) | the proof styles: (a) forward invariance of the guard then the self-loop, (b) exit into a successor's guard within one interval | `docs/WELLFORMED.md` §2 |
| the tool's sufficient check | `relcert --wellformed`: both clauses per right mode (clause (ii) as `ok (invariant)` / `ok (exit→S)`; clause (i): from every guard state the flow stays in the evolve domain for `ε_R` and does not blow up; else `UNKNOWN`, or `BLOCKING` when a guard state leaves the domain at once), strict in `--check-quick-v2` (181 right modes: 75 `ok (invariant)`, 106 `ok (exit)`, 0 `UNKNOWN`, 0 `BLOCKING`); not part of the guarantee, which takes `WellFormedR` | `Trusted/WellFormedCheck.lean`, `docs/WELLFORMED.md` §4 |
| the three satellites | their right evolve domains carry the conserved momentum band (total angular momentum about each wheel axis within the wheel's capacity), and Assumption 1 holds on that declared domain | `docs/WELLFORMED.md` §3 |

### 2.2 Definition 3 (segments), Definition 4 (witness strategy), Theorem 1, Lemma 3 and Lemma 4

The paper states two segment obligations (Definition 3), assembles them into a witness
strategy (Definition 4, a finite tree), and derives each obligation from a certificate: Lemma
3 (Proving Joint Segments, Section 4.2) gives `seg_joint(m_l, m_r, min(ε_l, ε_r/λ))` from
`flowC(m_l, m_r, joint, λ)` through Assumption 1, Lemma 1 and the box; Lemma 4 (Proving
Right-Only Segments, Section 4.3) gives `seg_r-only(m_r, ret(m_r))` from
`flowC(m_l, m_r, right-only, ·)` and the reposition certificate, the retained successors as
exits. Theorem 1 (Soundness of Witness Strategies, Section 3) says that witness strategies for
every admissible initial mode give the per-mode obligation Eq. 12 within `op_R`; its proof
(Appendix A.5, with Lemma 6, the claim at a node) is a structural induction on the strategy
tree with a per-node budget (`ε_l` minus the joint durations above), splitting the left flow
by autonomy at joint nodes, which mirrors the induction on the `CoveredX` derivation in
`coverX_piece`. In Lean none of the three statements is a standalone theorem with the paper's
∀∃ statement: `theorem3_of_coverX` goes from the certificate facts to the matching directly,
Theorem 1 is its cover induction and Lemmas 3 and 4 are steps of it (Appendix B.3).

| paper | Lean | where |
|---|---|---|
| the entry states of a segment: `φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r} ∧ m_r ∈ next(u)` (∧ `γ_σ` in setting σ; the paper reads every guard together with its mode's domain, the tool and Lean keep domains as a separate piece of the anchor, which is equivalent) | an anchor state `A l q`: the row, the envelope, the guard of `q` and the kept atoms of both modes; the kept atoms of `m_l` are the conjuncts of `I_{m_l}`, entered from the left guard (O1) and kept along the left flow (O2, the stay verdicts `atomsStayC_L`); the anchor implies both domains (`hAdom`); Lean's cycle starts after selection (`modeStep = ?(mv = q); ode_q; switch`) | `Proofs/Encoding/Emitted/Anchor.lean`, `Emitted/Stay.lean`, `Proofs/Encoding/JointBridge.lean` |
| `seg_joint(m_l, m_r, τ)`: from the entry states, `[|(F_{m_l}^{≤τ}, R^{m_r})⟩⟩ I_{m_l}` (the flow of `m_l` for at most `τ`, timer started at 0; one right cycle) | the joint cases of `coverX_piece`: the partial-span case is `coverX_finish`, the full-span branch of `step` inlines the same reasoning | `Proofs/Encoding/CoverResp.lean` |
| **Lemma 3** (Proving Joint Segments): `flowC(m_l, m_r, joint, λ)` gives, in every source setting σ, `seg^σ_joint(m_l, m_r, min(ε_l, ε_r/λ), ret^joint_σ(m_r))` | inside those cases: the right run of span `δ = ε_R/λ` exists by Assumption 1 clause (i); `joint_stretch` and the rescaling lemma `joint_of_sols_lam` (the forward direction of Lemma 1) pair it with the left run as one run of the joint product program; the certificate (`hbox`) keeps the anchor along it; the end state enables a declared successor by clause (ii) | `Proofs/Encoding/CoverResp.lean`, `ReplayEngine.lean`, `SyncSwitch.lean` |
| `seg^σ_r-only(m_r, S)` for a landing set `S` of right modes: with the left frozen, from the same entry states, `⟨R^{m_r}; R*⟩ (I_{m_l} ∧ land(S))`, `land(S) = ⋁_{q' ∈ S} (g_{q'} ∧ q' ∈ next(u))` (end state only; no intermediate state is constrained) | `RepoProgress G tr epsR …`: from a reposition start, right-only clocked cycles of the node until a retained exit is enabled, the anchor holding at the switch state; through the clocked chain `RRespPC` (the clocked twin of `RRespP`, which may pass through several modes, each cycle of duration `≤ ε_R`) it constrains only the end state; at least one segment, possibly of zero duration (`land_at_start`); consumed by `repoStep` inside `coverX_piece`; `S` is the retained successor set | `Proofs/Encoding/CoverResp.lean`, `ClockedRight.lean`, `Progress.lean` |
| **Lemma 4** (Proving Right-Only Segments): `flowC(m_l, m_r, right-only, ·)` and the reposition certificate give `seg_r-only(m_r, ret(m_r))`; the flow certificate may be checked on the restricted mode `m_R \| ¬landing target` only | `repoProgress_one`, `repoProgress_two`, `repoProgress_one_down`, and on the restricted mode (the pre-landing region) `repoProgress_one_reg`, `repoProgress_two_reg`, `repoProgress_one_down_reg` and the two-stage forms in either direction `repoProgress_two_ud_reg`, `repoProgress_two_du_reg`, `repoProgress_two_dd_reg`, with `first_hit`: the stage list, the right-only flow box (`hboxD`) and the right-only non-connection facts (`hpruneD`) prove `RepoProgress`; discharged per benchmark by `hrepoProg_of` and handed to `theorem3_of_coverX` as the `hrepoProg` field of `CoverHyps` | `Proofs/Encoding/Progress.lean`, `Emitted/Progress.lean` |
| **Definition 4** (Witness Strategy): a finite tree rooted at an initial right mode `q₀`, nodes right modes labelled with a segment in the node's setting σ (pre-joint iff no joint node above it); a joint node carries `seg^σ_joint(m_l, q, τ_q, S)` and a right-only node `seg^σ_r-only(q, S)`; the children are exactly the landing set `S`; a joint node is a leaf when the `τ`'s on its branch sum to at least `ε_l` | the cover `CoveredX` read as a tree: `step` is a joint node whose children are the retained successors, `stepRepoPre`/`stepRepoPost` a right-only node, `base` a leaf (the remaining budget fits one segment). The landing set is `retainedSucc` in the all-successors rules and the committed subset `S` of `stepChosen`, `repoChosen`, whose adequacy is the coverage certificate (`hcovJ`, `hcovR`, `hcovS` in `CoverHyps`, `docs/CHOICE-SOUNDNESS.md`) | `Checker/CoverX.lean`, `Proofs/Encoding/Theorem3General.lean` |
| **Theorem 1** (Soundness of Witness Strategies), with Lemma 6 (the claim at a node) | `coverX_piece`: the walk of the tree, one clocked left piece answered from a node of `CoveredX` (the segment runs, the anchor is kept, a child is entered legally, the budget decreases); `coverX_gresp` lifts it to `GResp` over one left window; the window assembly `Hmulti_of_coverX` splits the left execution into windows and quantifies over the admissible starts | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| an older single-segment route (not used by `theorem3_of_coverX`) | `segment_faModal` and `segment_relational`: ∀∃ segment theorems with a carried duration-existence side condition | `Core/Reify.lean`, `Proofs/Encoding/EncodingBridge.lean` |

## 3. Section 4.1: flow certificates (Lemma 1, Definition 5, Lemma 2) and the discharge of mode facts

| paper | Lean | where |
|---|---|---|
| the joint product program (Eq. 14): `ẋ_L = f_L`, `ẋ_R = λ f_R`, under both evolve domains | `Program.ode (jointSys fL fR (Term.const λ)) (domL ∧ domR)` | `Core/FlowCert.lean` |
| the right-only product program (Eq. 15): left frozen | `rightBlock fR` with the left coordinates unmoved (`mergeLR`), the dynamic reposition program | `Proofs/Encoding/ReplayDyn.lean`, `RepoPrefixR.lean` |
| **Lemma 1** (Time Stretching): for constant `λ ≥ 0`, `φ` solves `ẋ = f` on `[0, λτ]` iff `s ↦ φ(λs)` solves `ẋ = λf` on `[0, τ]` | the statement: `odeSol_stretch_iff` (any ODE system with its domain, `ẋ = λf` as `stretchSys λ`, `0 ≤ λ`, `0 ≤ τ`; `λ = 0` included) and its right-model form `odeSol_rightBlock_stretch_iff`; both audited in `InstancesV2/AxiomCheck.lean`, three standard axioms. Related: `sem_rightBlock_reparam`, `sem_rightBlock_reparam_iff` (`λ > 0`, the stretched and real right blocks have the same runs); `odeSol_right_of_joint`; the joint rescaling used by the cover induction, `joint_of_sols_lam` (`λ ≥ 0`, forward direction) | `Proofs/Encoding/Stretching.lean`, `Proofs/Encoding/Reparam.lean`, `Emitted/Region.lean`, `SyncSwitch.lean` |
| **Definition 5** (Flow Certificate): `flowC(m_l, m_r, kind, λ)` holds if `entry(m_r) → [α_kind^λ] I_{m_l}` is valid | the box as the general theorem consumes it: the `hbox` field of `CoverHyps` (joint kind: the anchor kept along every run of the stretched joint flow from an anchor state, the anchor carrying both modes' kept atoms) and the hypothesis `hboxD` of the `repoProgress_*` lemmas (right-only kind: the anchor kept along the frozen-left flow); per segment `couple_box_cutX` (joint) and `couple_box_dyn` (right-only) | `Proofs/Encoding/Theorem3General.lean`, `Progress.lean`, `SyncSwitch.lean`, `ReplayDyn.lean` |
| Eqs. 16 to 18: the Lie-derivative conditions over the domain and the mode facts `I_{m_l} ∧ I_{m_r}`; "Discharging the obligation." (certification in rounds, a component's condition may assume the components of earlier rounds) | the three query routes of one component: whole-domain `dom ∧ ġ > 0` (route A), boundary `dom ∧ g = 0 ∧ ġ ≥ 0` (route B), superlevel `dom ∧ g ≥ 0 ∧ ġ > 0` (route C), each `unsat`; the pack of a pairing `(l, q)` at its stretch: one `unsat` per component by any route, over the segment domain narrowed by the kept atoms, in the strata order the tool recorded (`modalVerdXQueries`); the right-only pack `modalVerdDynXQueries` | `Core/FlowCert.lean` (`flowQuery`, `flowQueryStrict`, `lieDeriv`, `tderiv_correct`), `Proofs/Flow/DISuperlevel.lean`, `Proofs/Flow/StratifiedBarrier.lean` (rounds), `VerdictsV2/ModalX.lean`, `ModalDynX.lean` |
| **Lemma 2** (Lie Conditions): the conditions over the domain strengthened by `I_{m_l} ∧ I_{m_r}`, when both are mode facts, prove the box of Definition 5 | `flow_cert_sound` (one component: an `unsat` route query gives `BoxLe` along the stretched joint flow, through dL-lean's `DI_nonstrict_domain`); threaded over the components with the kept atoms by `check_sound_multi_cutX` | `Core/FlowCert.lean`, `Proofs/Soundness/CutLiftX.lean` |
| "Selecting the stretch." (Section 4.1) and "Flow certificates and the stretch." (Section 6.1): one stretch per left mode, tried as `ε_R/ε_L`, then 21 grid values of the declared range, 0 last and only when the range includes it; else a stretch per pairing; every joint segment lasts `min(ε_L, ε_R/λ_max)` | the stretch per pairing `lam l q`, the common span from `lamQ l`, the budget `⌈ε_L/δ⌉` (`Emitted/Data.lean`); the stretch of every pairing read from the emitted cover record by the bridge instance; a stretch-0 pairing admitted by `Emitted.timeOK` only when the record has `lambdaMin = 0` | `Trusted/OracleAPI.lean`, `Emitted/Data.lean` |
| "Mode facts." (Section 6.1): preprocessing tries atom kinds (a guard conjunct, the closure of a strict one, the set-point half-line of a contraction field) and keeps the mode facts | the checked cut, the Definition 2 row of §2 (`OracleAPI.checkedCut` / `checkedCutX`, `EvolStrengtheningX`, the stay verdicts, `CutLiftX`) | `Trusted/OracleAPI.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean` |
| the tool's query, the runner's query and the theorem's hypothesis are the same formula (Appendix B.4, "Pinning the queries.") | the runner rebuilds each query from the committed records with the tool's own lowering and printer through `bridgeGroups`; the bridge instance's `Verdicts` hypothesis is obtained from `GroupsOK` by `verdicts_of_groups`, its stretches read from the emitted cover record | `VerdictsV2/`, `Proofs/Encoding/Emitted/Run.lean` |

Existence of the right flow for the needed duration is not part of Definition 5 or Lemma 2 in
the paper; Lemma 3 draws it from Assumption 1, and so does Lean (clause (i), §2.1).

## 4. Section 4.2: non-connection certificates (Definition 6)

| paper | Lean | where |
|---|---|---|
| the programs `β_joint` (one cycle of the right mode; the stretch is dropped by Lemma 1) and `β_right-only` | the right flow of the stretched joint program and the frozen-left flow, as under Definition 5 | `Core/FlowCert.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| **Definition 6** (Non-Connection Certificate): proves `entry_σ(m_r) → [β_kind] ¬g_{m'}` (guards read with their domains; the tool's query keeps the domains explicitly, which is equivalent) | the two checks as the tool sends them, `NonConn.queries` (source: no entry state of `m_R` satisfies the threshold guard; barrier: on the threshold the flow moves the variable away), defined once for the certifier, the runner and the kernel | `Trusted/NonConnQuery.lean` |
| the consequence sentence after Definition 6: the declared change is never taken under `(σ, kind)` | `nonconn_sound` (dL-lean `DI_strict` on the safe-side term); `nonconn_of_unsat`: the runner's two `unsat` answers are its hypotheses | `Checker/NonConn.lean`, `Proofs/Encoding/NonConnBridge.lean` |
| the retained successors `ret^κ_σ(q)` are the exits segments of kind κ reach | `SearchGraph.retainedSucc` drops a pruned edge; the cover record carries the `pruned` list the kernel replays; in `coverX_piece` the end state of a joint segment enables a declared successor (Assumption 1 clause (ii)) whose guard is excluded for every pruned exit (`guard_pos_of_barrier`), so the retained set still serves as the exit set | `Checker/Cover.lean`, `Checker/CoverX.lean`, `Proofs/Encoding/Emitted/Barrier.lean` |
| where it enters Theorem 3 | the bridge keeps the barrier term of every pruned exit of the current right mode in the anchor: `≤ 0` on entry (source check), kept along joint and frozen flows (barrier check), `> 0` under the target's guard (`nonconn_entry`, `nonconn_keep`, `guard_pos_of_barrier`; the `hprune` field of `CoverHyps`, and `hpruneD` of the `repoProgress_*` lemmas for the right-only kind) | `Proofs/Encoding/Emitted/Barrier.lean` |
| "Pruning." (Section 6.1): a threshold guard on one variable, no entry state satisfies it, the flow points away on the threshold | over the suite 16 pruned edges, 32 non-connection queries (`--check-quick-v2`, and as groups of `relcert-bridge-verdicts`) | `Checker/NonConn.lean`, `Trusted/NonConnQuery.lean`, `VerdictsV2/RunV2.lean` |

## 5. Section 4.3: reposition certificates (Definition 7, Lemma 4) and "Reposition." of Section 6.1

The paper calls them reposition certificates; the tool and Lean call them progress
certificates (`Trusted/ProgressEmit.lean`, `Proofs/Encoding/Progress.lean`,
`VerdictsV2/ProgressPin.lean`, `relcert-progress-verdicts`).

| paper | Lean | where |
|---|---|---|
| the region of the stage list, `R ≡ I_{m_l} ∧ I_{m_r} ∧ φ_inv(m_l)` ("Reposition.", Section 6.1; the tool's region adds the right evolve domain); retained successors `ret(q)` = declared, non-self, not pruned | the node's region (the anchor `A q`, its kept atoms, the right domain); `retainedSucc` | `Checker/Cover.lean`, `Emitted/Anchor.lean` |
| **Definition 7** (Reposition Certificate): `entry^σ(m_r) → ⟨R^{m_r}; (R^{m_r})*⟩ land(ret_σ(m_r))` is valid, `entry^σ(m_r) = φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r} ∧ m_r ∈ next(u_r) ∧ γ_σ` | the conclusion of the `repoProgress_*` lemmas, `RepoProgress`: from a reposition start, cycles of the node until a retained exit is enabled, the anchor kept | `Proofs/Encoding/CoverResp.lean` |
| the stage list (one or two stages, each a variable, a threshold and a rate): rate, keep and landing obligations; the landing target is the closed half-space past the last threshold | per reposition node: staged rate bounds (`rateQuery`), kept thresholds (`keepQuery`) and the landing (`landQueries`: on the crossing line and at an already-crossed start some exit's guard holds); emitted by default (`RELCERT_NO_PROGRESS=1` disables it) | `Trusted/ProgressEmit.lean` |
| the progress argument (Section 6.1): with the right-only flow certificate on the restricted mode, the stage list implies the reposition certificate, since the first uncrossed stage gains at least `r_i ε_R` per cycle | `repoProgress_one`, `repoProgress_one_down` (a single downward stage), `repoProgress_two` and the `_reg` forms (hypotheses include the right-only flow box `hboxD` and `hpruneD`), standard axioms; `progressVerd_one`, `progressVerd_one_down`, `progressVerd_two` read the runner's `unsat` answers as its facts | `Proofs/Encoding/Progress.lean`, `VerdictsV2/ProgressPin.lean` |
| **Lemma 4** (Proving Right-Only Segments) | a step of `coverX_piece`, §2.2: `hrepoProg_of` folds the stage facts, the right-only flow box `hboxD` and the right-only non-connection facts `hpruneD` into `RepoProgress`, the `hrepoProg` field of `CoverHyps`, consumed by `repoStep` | `Proofs/Encoding/Emitted/Progress.lean`, `CoverResp.lean` |
| suite | 1009 progress groups, all discharged (`relcert-progress-verdicts`); 950 reposition queries re-sent by `--check-quick-v2` | `docs/THEOREM3-GENERAL.md` §3, `docs/PRELANDING.md` |

Why the premise is needed: Assumption 1 may enable only the self-loop at the end of a
right-only cycle, the right-only case of Definition 8 needs a non-self exit, and nothing in
Definition 5 says one is reached. The general theorem therefore takes
`hrepoProg : RepoProgress …`, which the reposition certificate discharges.

## 6. Section 5: the cover and Theorem 3

### 6.1 Definition 8 (cover)

| paper | Lean | where |
|---|---|---|
| configuration `(m_R, B, σ)` with budget `B` and source setting `σ ∈ {pre-joint, post-joint}` | `Config = ⟨q, B, SrcSetting⟩`, `B : ℕ` segments (the budget `⌈ε_L/δ⌉`, `δ` the common span) | `Checker/Cover.lean` |
| "Search graph.": the certified segment durations `τ_{m_r} = min(ε_l, ε_r/λ)`; node kinds from Lemma 3 (joint) and Lemma 4 (right-only) | the segment span `δ`, `B` segments per window; the cover flags `jointOK` and `dynPre`/`dynPost` | `Checker/CoverEmit.lean`, `Emitted/Data.lean` |
| **Lemma 5** (Covers Are Witness Strategies): a cover from `(q₀, ε_l, pre-joint)`, viewed as a tree, is a witness strategy (Definition 4): children = the retained successors of the node's kind, the exits of Lemmas 3 and 4 | no separate reading: `coverX_piece` walks `CoveredX` directly (§2.2); `SearchGraph.retainedSucc` is the landing set of a joint node, the exits of a right-only node are the retained exits of `RepoProgress`; for a committed subset the chosen set `S` is the landing set certified by its coverage certificate (`hcovJ`, `hcovR`, `hcovS`) | `Proofs/Encoding/CoverResp.lean`, `Checker/Cover.lean` |
| finish case: a prefix of the certified joint segment finishes the left cycle | `CoveredX.base` | `Checker/CoverX.lean` |
| continue case, joint kind: every retained successor covered at `B − w` with `σ' = post-joint` | `CoveredX.step` | `Checker/CoverX.lean` |
| continue case, right-only kind: every retained exit covered, `σ` unchanged | `CoveredX.stepRepoPre`, `stepRepoPost` | `Checker/CoverX.lean` |
| continue case, committed successor subset: every target of a committed subset covered, the segment certified with that subset as landing set | `CoveredX.stepChosen` (joint), `repoChosen` (right-only), `hop`; the landing set from the coverage verdicts `hcovJ`/`hcovR`/`hcovS` (the region implies some guard of the subset) | `Checker/CoverX.lean`, `Proofs/Encoding/CoverResp.lean` |
| "Covered configurations.": only configurations reached by finitely many applications | `CoveredX` is inductive; the checker `decideCoveredX` is fuel-bounded (`fuelOf`); `decideCoveredX_sound` says an accepted configuration is covered | `Checker/CoverX.lean` |
| the search graph: certified kinds, weights, retained edges | the emitted cover record `CoverEmitE` (flags per node: `jointOK`, `dynPre`/`dynPost`; stretches; pruned edges; admissible starts; strata orders) replayed in the kernel: `coversOK` (bridge, `decide +kernel`) | `Checker/CoverEmit.lean`, `Emitted/Keyed.lean` |
| admissible initial right mode `q₀` for `m_L` | `AdmissibleStart gL φ env (guard q) (cuts q)`: some joint state in the left guard, the invariant, the envelope and the right region; the dropped starts are those whose admissibility query is `unsat` (`Bridge.admQueryOf`, `adm_sound`) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Barrier.lean` |
| "The cover." (Section 6.1): depth-first recursion, budget-neutral cycles rejected, committed subsets tried when no cover closes | `OracleAPI.certifyWithData`: the same recursion over configurations, untrusted; its output is replayed as above | `Trusted/OracleAPI.lean` |

The committed-subset cases `stepChosen`, `repoChosen` and `hop` are the tool's default
(`RELCERT_NO_CHOICE=1` disables them). Twelve suite benchmarks need them (Table 1, letter X),
seven of them from the literature: `lit_csf21_vehicle_bus`, `lit_csf21_vehicle_thermo`,
`lit_drl_lane_control`, `lit_freedm_meter`, `lit_girard08_robot`,
`lit_gpt10_boost_converter`, `lit_lz21_vehicle_position` (`docs/paper-numbers/letters.md`).
The two exhibits of `benchmarks/choice/` use them too; `docs/CHOICE-SOUNDNESS.md`.

### 6.2 Theorem 3 (soundness of synthesis)

> `str(φInv) → [|(L*,R*)⟩⟩ str(φInv)` (Eq. 10) if (1) `R` satisfies Assumption 1; (2) for
> every `m_L` every admissible `q₀` admits a cover from `(q₀, ε_L, pre-joint)` at
> `φ_inv(m_L)`; (3) every declared left mode change satisfies the handoff condition (Eq. 13).

Mechanized as `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`, standard axioms
only; the Z3 axiom enters only through the instances' verdict hypotheses). Its right program is
the clocked automaton `rightAutomatonBodyC Gr (Aux, a) (Aux, d) epsR` (§9: each cycle flows for
at most `ε_R`, the cap as a post-test); the right clock `tr = (Aux, d)` is a parameter of
`CoverHyps` and of `RepoProgress G tr epsR …`, whose responses are the clocked relation
`RRespPC`; the only hygiene facts are `tr ∉ range Lv` and `tr ∉ range Rv`. The paper proves
Theorem 3 by Theorem 2 (Composition), which applies Theorem 1 per left cycle and the handoff
condition at left mode changes. In Lean the theorem goes from the certificate facts to the
matching directly; Theorem 1 is its cover induction and Lemmas 3 and 4 are steps of it (§2.2,
Appendix B.3).

| paper condition | Lean hypothesis | discharged in an instance by |
|---|---|---|
| (1) Assumption 1 | `hwf : WellFormedRIn Gr guard reg epsR` | the benchmark's `WellFormedR` lemma (§2.1) at its own dimension `n0`, transported onto the pruned graph (`wellFormedR_transport`) and lifted to the instance dimension `n0 + 1` by `wellFormedR_lift` under the decided bundle `padOK IR n0 = true` (`decide +kernel`) |
| (2) the covers, per `m_L` and admissible `q₀` | `hcov : ∀ l q, AdmissibleStart … → CoveredX Gr (ch l) ⟨q, B l, preJ⟩`, with `hdt : dt ≤ B l · δ l` (the window fits the budget) | covered starts by `decideCoveredX` on the emitted record (`coversOK`), the other starts inadmissible by their `unsat` (`adm_sound`) |
| (2), what each cover step consumes (Definitions 5, 6 and 7, Appendix B.1's `CoverHyps`) | `H : ∀ l, CoverHyps …`, whose fields are: the flow certificate of every certified joint pairing at its stretch (`hbox`); the non-connection certificates of the pruned edges (`hprune`); the entry condition (`hhand`: the anchor of `q` and the guard of `q'` give the anchor of `q'`); the reposition-progress premise (`hrepoProg : RepoProgress …`, §5); the coverage certificates of committed subsets (`hcovJ/R/S` with their regions `hRJ/RR/RS`); and the side conditions `hlam`, `hspan`, `hAfv`, `hAdom`. The right-only flow box (`hboxD`) and the right-only non-connection fact (`hpruneD`) are hypotheses of the `repoProgress_*` lemmas, folded into `RepoProgress` when it is discharged | the bridge's `coverHyps_of` from the `Verdicts` structure (`Emitted/Keyed.lean`); `hrepoProg` by `hrepoProg_of` (`Emitted/Progress.lean`) |
| the loop invariant's right bookkeeping (`op_R`) | the anchor `A l q` (`hAstart`, `hApost`): the row, the kept atoms of both modes, the barrier terms of `q`'s pruned exits, the envelope; its region part `regionG guard cuts q` | `Emitted/Anchor.lean` (`AG`, `AG_start`, `AG_post`) |
| (3) the handoff condition (Eq. 13): `φ_inv(m_L) ∧ dom_{m_L} ∧ guard_{m_L'} ∧ dom_{m_R} → φ_inv(m_L')` for a change from `m_L` to `m_L' ∈ next(m_L)` ("Handoff.", Section 6.1: one query per declared left mode change, negating Eq. 13) | for mode-dependent rows, the hypothesis `hhand` of `theorem3_modeKeyed`; the runner's query `Handoff.queryOf` is exactly this implication with the declared domains conjoined (`handoff_of_unsat`, `handoff_sound`) | `Proofs/Encoding/ModeHandoff.lean`, `Trusted/Handoff.lean`, `Emitted/Barrier.lean` |
| the conclusion | `rvalid (theorem3Form (bigChoice (leftProgsOf …)) (rightAutomatonBodyC Gr (Aux, a) (Aux, d) (epsR p)) ((canonInvM g gs ∧ envLR domL domR) ∧ mvRegionR (Aux, a) (regionG guard cuts) …))`: one declared row (`windowClaim p n cX cov reg a b d dt`); for per-mode rows the composition through `theorem3_modeKeyed_gen` over `leftAutomatonBody` with `psiK` (`keyedClaim p n cX cov reg a b c d dt`) | `Emitted/Window.lean`, `Emitted/Keyed.lean`, `ClockedKeyed.lean` |
| the per-benchmark theorem, mode-keyed form (18 suite benchmarks) | `theorem3_keyed_of_records (hv : Verdicts p n cX cov prog ce) (hpo : progOK …) (hcovers : coversOK …) (hregR : reg.fv ⊆ range Rv) (hinv : RegionInvariant …) (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) (a b c d : Fin n) … (dt : ℝ) (hdt : dt ≤ epsL p) : keyedClaim p n cX cov reg a b c d dt`; the generated instances take `a b c d = 0 1 2 3` and `reg = ⊤` | `Emitted/Keyed.lean`; `InstancesV2/Bridge/<B>.lean` |
| the per-benchmark theorem, window form (32 suite benchmarks) | `theorem3_window_of_records … (hwf : WellFormedRIn …) (hsame : rowsSame p = true) (a b d : Fin n) … (dt : ℝ) (hdt : dt ≤ epsL p) : windowClaim p n cX cov reg a b d dt`; the generated instances take `a b d = 0 1 2` | `Emitted/Window.lean` |
| right-only certificates on the restricted mode (41 suite benchmarks and both exhibits) | `theorem3_window_of_records_pl`, `theorem3_keyed_of_records_pl`: the same conclusions over the cover merged with its pre-landing record (`withPL cov pl`, `plOK`) | `Emitted/Window.lean` |
| the proof: Theorem 1 on the cover read as a witness strategy, plus the handoff condition | `coverX_piece`: per case of `CoveredX`, the segment runs (Assumption 1 clause (i)), the anchor is preserved (Definition 5), the end state enables a declared successor (clause (ii)) that is not pruned (Definition 6), the switch is legal and the entered anchor holds (`hhand`); the budget decreases; the joint cases are Lemma 3 and the right-only cases (`repoStep`, from `RepoProgress`) Lemma 4; `coverX_gresp` and `Hmulti_of_coverX` assemble the windows; the handoff condition enters through `theorem3_modeKeyed_gen` | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean`; `docs/THEOREM3-GENERAL.md` §2 |

The mode-dependent case: `theorem3_modeKeyed_gen` (the clocked twin of
`ModeHandoff.theorem3_modeKeyed`) composes the per-mode window responses with the handoff
condition and the side conditions on `u_L` (freshness, footprints; `sides_disjoint4` for the
four auxiliary coordinates); the bridge supplies the per-mode responses through
`hstepMode_GRC` and `HMode_regionGC` (`ClockedKeyed.lean`). Mode-independent rows take the
window form directly (`rowsSame` decided).

## 7. Section 6: implementation and evaluation

| paper | Lean / tool | where |
|---|---|---|
| "Mechanization." (Section 6): Theorem 3 mechanized over the programs of Eq. 1 with one evolution domain per system; the certificates, mode facts, handoff conditions and Assumption 1 are hypotheses of the Lean theorem, the other results proof steps; each benchmark an instance built from the tool's records; Lean lemmas tie the pruning query, stage lists and committed subsets to the certificates; each Z3 `unsat` a hypothesis on the printed query under one axiom; Assumption 1 per benchmark without Z3; trust base = parser and lowering, query printer, Z3 `unsat`, kernel with the statement of Theorem 3 | §0, §6.2, §2.1, §2.2, §9; counts in `docs/CERTIFICATION-CHECK.md` | `RelCertifier/Trusted/README.md` |
| Section 6.1: "a Lean 4 executable; its search is untrusted, a kernel-verified checker replays every cover it proposes"; every obligation one polynomial query discharged by Z3, only `unsat` certifies | `relcert` (`Main.lean`); the trusted surface, file by file, in `RelCertifier/Trusted/README.md`: parser (`Parse.lean`, `KeyAudit.lean`), lowering (`Run.lean`, `JointVars.lean`, `InvComponents.lean`, the query builders `Handoff.lean`, `NonConnQuery.lean`, `BridgeQueries.lean`, `ProgressEmit.lean`, `ChoiceEmit.lean`), printer (`Smt.lean`), Z3 (`Z3.lean`, `Oracle.lean` with the axiom), the untrusted certifier `OracleAPI.lean` | `RelCertifier/Trusted/` |
| "Mode facts." | §2 (Definition 2 row), §3 | `Trusted/OracleAPI.lean`, `Checker/EvolStrengtheningX.lean` |
| "Flow certificates and the stretch." | §3 | `Trusted/OracleAPI.lean`, `Emitted/Data.lean` |
| "Pruning." | §4 | `Trusted/NonConnQuery.lean` |
| "Reposition." | §5 | `Trusted/ProgressEmit.lean` |
| "Handoff." | `Handoff.queryOf`; 2846 handoff queries re-sent by `--check-quick-v2`, all `unsat` (`docs/HANDOFF.md`) | `Trusted/Handoff.lean` |
| "The cover." | §6.1; `decideCoveredX` with fuel is the kernel's replay of the same recursion | `Checker/CoverX.lean` |
| Table 1 (Section 6.3, the suite by area, letters S M R B P D I X, used and needed), the baseline (Sync) and the ablation counts; Table 2 (Section 6.4, the refinement ladders: the rover ladder `rover_ladder_{2to3,3to6,6to8,8to12}` and the stop-line ladder `stopline_{lag,friction,tyre,drag}`) | `scripts/paper_numbers.sh` (the frozen run; output in `docs/paper-numbers/`: `numbers.tex`, `table1.tex`, `MANIFEST.txt`), `scripts/suite_v2_letters.py` (`letters.md`), `scripts/suite_v2_matrix.py` (`matrix.md`) | `docs/paper-numbers/`, `benchmarks/README.md` |
| "Known-false inputs." (Section 6.3) | §8 | `docs/REFUTATION-RESULTS.md` |

## 8. Where the numbers come from

Every count below is the paper's (its macros are copied from `docs/paper-numbers/numbers.tex`
and from `docs/CERTIFICATION-CHECK.md`), and is checked against a declared total in the code.

| number | source |
|---|---|
| 50 benchmarks (10 from the literature), all certified with `RELCERT_IMPLIED_CUT=1`; Table 1 letters, Sync and ablation counts, Table 3 rows | `scripts/paper_numbers.sh` (`docs/paper-numbers/`), `scripts/suite_v2_letters.py`, `benchmarks/suite_v2/` |
| 52 bridge instances (50 suite, 2 exhibits), 13677 verdict groups | `InstancesV2/Bridge.lean`, `relcert-bridge-verdicts`, `expectedBridgeGroupsV2` (`VerdictsV2/RunBridge.lean`) |
| `--check-quick-v2`: modal 1421, handoff 2846, non-connection 32 (16 pruned edges), reposition 950; strict Assumption 1 gate 181 right modes (75 invariant, 106 exit) | `expectedModalV2`, `expectedHandoffV2`, `expectedNonConnV2`, `expectedPrunedEdgesV2`, `expectedDynV2`, `ExpectedSuiteV2.wfModes` (`VerdictsV2/RunV2.lean`) |
| 1009 progress (reposition certificate) groups | `relcert-progress-verdicts`, `expectedProgressV2` (`VerdictsV2/RunProgress.lean`) |
| 140 kernel refutations, 416 verdict groups; the experiment: 1193 mutants, 398 certified, 140 refuted, 655 open | `InstancesV2/Refute.lean`, `relcert-refute-verdicts`, `expectedRefuteGroups` (`InstancesV2/Refute/Table.lean`); `docs/REFUTATION-RESULTS.md`, `docs/refute/` |
| Assumption 1: 50 of 50, Z3-free; 78 axiom lines (76 standard, 2 `CutLiftX`) | `InstancesV2/WellFormedBattery.lean` |
| axioms of the generic theorems and Theorem 3's route (`theorem3_of_coverX`, the four record-level theorems): 16 lines, 9 at `propext`, `Classical.choice`, `Quot.sound`, 7 adding `z3_unsat_sound` | `InstancesV2/AxiomCheck.lean`; `docs/CERTIFICATION-CHECK.md` check 2 |

## 9. Modelling choices (Appendix B.2)

| paper | mechanized | direction |
|---|---|---|
| right clock: `t := 0; {…, t' = 1 & t ≤ ε_R}` on the right | the right body of every bridge claim is `rightAutomatonBodyC G mv tr dt` (`ClockedTop.lean`, `clockedSeg` in `BridgeReposition.lean`) with `dt = epsR p`, per mode `q`: `?(mv = q); tr := 0; {x' = f_q, tr' = 1 & Q_q}; ?(tr ≤ ε_R); switch`. The cap is a post-test after the flow; since the clock is monotone from `tr = 0`, it admits exactly the same runs as `& t ≤ ε_R` inside the domain (the left side uses the same form, `gwindowSeg`). The right clock is the fourth auxiliary coordinate `(Aux, d)`, next to `(Aux, a)` (right mode variable), `(Aux, b)` (left clock), `(Aux, c)` (stored left mode); the instance dimension is the Assumption 1 lemma's dimension plus one (`bridgeDimV2`, `VerdictsV2/RunBridge.lean`; the lift `wellFormedR_lift` with the decided bundle `padOK`, `Emitted/Lift.lean`). The response layer is `gsegC`/`RRespPC`/`guarded_rights_bridgeC` (`ClockedRight.lean`); every right flow the chain builds has an explicit duration `≤ ε_R`. Clock erasure, `star_bodyC_to_body` (`ClockedRight.lean`), shows the clocked claim implies the unclocked one | exact (cap as post-test) |
| rotation: select then flow (right) | flow then select (`modeStepC`; `modeStep` in the unclocked layer): the same body up to rotation; the loop invariant therefore carries the right's current-mode guard (`op_R`) | rotation |
| budgets `B = ε_L`, weights `w = ε_R/λ` (real) | `B : ℕ` segments of the common span `δ`, `B = ⌈ε_L/δ⌉` (span `ε_L`, budget 1, when every pairing has stretch 0) | ℕ-discretization |
| resets | identities: only the stored mode and the timer are reset | exact |
| guards on left selection and right transitions | lowered once, in the trusted layer; every edge carries `hostGuard … (mR e.tgt)`, the same lowering as the left guards; the left program is `leftAutomatonBody` with the lowered left guards, the declared `next` lists and `u_L`, windows clock-capped (mode-independent rows through `bigChoice` of the windows, carried by `theorem3_leftAut_of_choice`) | exact |
| domains | each side's uniform evolve domain (every suite benchmark declares the same evolve in all modes of a side; `scripts/check_one_domain.py`); per-mode domains are outside the Lean lift | scope |
| invariant `φInv` | `φInv ∧ envLR domL domR ∧ mvRegionR mv (regionG guard cuts)` (`psiK` adds `u_L ∈ modes` in the keyed form) | the `str(φ)` form of Eq. 10: `mvRegionR` is `op_R` (with the mode facts), `envLR domL domR` is `Q_{u_l} ∧ Q_{u_r}` |

## 10. Appendices of the paper

Appendix A (Proofs) proves each numbered result on paper; the Lean names that carry the same
argument:

| appendix | paper result | Lean |
|---|---|---|
| A.1 | Lemma 1 (Time Stretching) | `odeSol_stretch_iff` (the statement, `λ ≥ 0`; right-model form `odeSol_rightBlock_stretch_iff`; `Proofs/Encoding/Stretching.lean`); related: `sem_rightBlock_reparam_iff` (`λ > 0`, same-runs form, `Proofs/Encoding/Reparam.lean`), `joint_of_sols_lam` (`λ ≥ 0`, used by Theorem 3, `Proofs/Encoding/SyncSwitch.lean`) |
| A.2 | Lemma 2 (Lie Conditions), with "Mode facts across cycles." | `flow_cert_sound` (`Core/FlowCert.lean`), threaded over the components with the kept atoms by `check_sound_multi_cutX` (`Proofs/Soundness/CutLiftX.lean`) |
| A.3 | Lemma 3 (Proving Joint Segments), with "Committed subsets." | the joint steps of `coverX_piece` (`Proofs/Encoding/CoverResp.lean`), with the non-connection facts `nonconn_sound` (`Checker/NonConn.lean`) and `nonconn_of_unsat` (`Proofs/Encoding/NonConnBridge.lean`) |
| A.4 | Lemma 4 (Proving Right-Only Segments), with "Committed subsets." | the right-only steps of `coverX_piece` (`repoStep`), from `RepoProgress` (`CoverResp.lean`), discharged by `repoProgress_one`, `repoProgress_two`, `repoProgress_one_down` and their `_reg` forms on the restricted mode, including `repoProgress_two_ud_reg`, `repoProgress_two_du_reg`, `repoProgress_two_dd_reg` (`Proofs/Encoding/Progress.lean`) |
| A.5 | Theorem 1 (Soundness of Witness Strategies), with Lemma 6 (the claim at a node) | the induction `coverX_piece` over `CoveredX`; Lemma 6's per-node claim is what `coverX_piece` states per covered configuration (every left run within the remaining budget is answered by the right); `coverX_gresp` and `Hmulti_of_coverX` lift it to the left windows |
| A.6 | Theorem 2 (Composition) | `theorem3_modeKeyed_gen` (`Proofs/Encoding/ClockedKeyed.lean`), the handoff queries read by `handoff_of_unsat` (`Proofs/Encoding/ModeHandoff.lean`) |
| A.7 | Lemma 5 (Covers Are Witness Strategies) | `CoveredX` (`Checker/CoverX.lean`) read as the tree, `decideCoveredX_sound` (the kernel's replay of the emitted cover) |
| A.8 | Theorem 3 (Soundness of Synthesis) | `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`), per benchmark `theorem3_window_of_records`, `theorem3_keyed_of_records` and their `_pl` forms (`Emitted/Window.lean`, `Emitted/Keyed.lean`) |

Appendix B (The Mechanization):

| appendix | here |
|---|---|
| B.1 What Is Proved | §6.2 (`theorem3_of_coverX`, `CoverHyps`, the four record-level theorems, the eight `Verdicts` families, the five decided structural facts) and §0 (52 instances, 32 window, 18 keyed, 41 `_pl`, 5 demo and strict files) |
| B.2 The Lean Statement and Eq. 1 | §9 |
| B.3 Where the Paper Lives in Lean | this whole file; its table is §2 to §6 |
| B.4 Trusted Base | §7, the last row of §3 ("Pinning the queries."), `RelCertifier/Trusted/README.md`; `InstancesV2/AxiomCheck.lean` (16 lines) |
| B.5 Assumption 1 | §2.1 and `docs/WELLFORMED.md` |
| B.6 Refutations | the row below and `docs/REFUTATION-RESULTS.md` |
| B.7 Reproduction | `docs/CERTIFICATION-CHECK.md` (the commands and their expected output) and `README.md` |

Refutations (Section 6.3 "Known-false inputs.", Appendix B.6): 140 invariant variants proved to
admit no certificate; `relcert` declines all 140 (`benchmarks/refute_mutants/*`,
`docs/refute/decline_default_budget.tsv`). Per variant, `¬ keyedClaim IR n cX cov ⊤ 0 1 2 3 dt`
or `¬ windowClaim IR n cX cov ⊤ 0 1 2 dt` (the clocked claims of the bridge instances, at the
benchmark's bridge dimension `RefRec.dim + 1`) for every cover record (any pruning), at the
model's mode-fact certificate: the generic `refute_keyed_C`, `refute_keyed_A`,
`refute_keyed_B`, `refute_window_B` refute the unclocked `keyedClaimU`/`windowClaimU`, and the
wrappers `refute_keyed_C_clocked`, `refute_keyed_A_clocked`, `refute_keyed_B_clocked`,
`refute_window_B_clocked` conclude against the clocked claims by contraposition through
`keyedClaim_to_unclocked` / `windowClaim_to_unclocked` (hypotheses `namesOK`, `cutsOK`,
`d ≠ a`); instances generated by `scripts/gen_refute.py` from the untrusted finder
`scripts/refute_finder.py`; 416 Z3 groups discharged by `relcert-refute-verdicts`
(`Proofs/Encoding/Emitted/Refute.lean`, `RefuteFlow.lean`, `RefuteExit.lean`,
`InstancesV2/Refute/`).

Appendix C (Per-Benchmark Results): Table 3 (`tab:per-benchmark`) is
`docs/paper-numbers/table_per_benchmark.tex`, generated by `scripts/suite_v2_letters.py` from
the frozen run's matrix.

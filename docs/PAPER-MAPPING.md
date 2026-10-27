# Paper ↔ mechanization: the map

Read this with the paper open. One section per formal element of the paper, in the paper's
order; each says what the Lean name is, where it lives, how its hypotheses are discharged, and
which axioms it rests on. Paper references are to *Certifying Forall-Exists Invariants for
Cyber-Physical Systems via Witness Construction*, the HSCC+ICCPS 2027 submission, in the
submission's numbering, Appendices A to C included (§10 maps the appendices). The repository
layout and the build and check recipe are in `README.md` and `docs/CERTIFICATION-CHECK.md`; the
historical, branch-by-branch account that this file replaces is
`docs/history/PAPER-MAPPING-2026-10-10.md` on branch `archive/legacy-2026-10` (the
`docs/history/` directory was archived on 2026-10-22).

**The numbering, verified against the submission's `paper.aux`.** Every numbered paper
reference in this repository's current documents, comments and docstrings is checked against
this table; the dated historical records that predate the submission say so at their top.

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
| Lemma 6 (Node Claim), inside the proof of Theorem 1 | `app:lem-node-claim` | A.5 |
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

Eqs. 2, 5 and 11 are unlabelled displays (the water tank's mode program, the running
example's ∀∃ invariance, and its `str`).

**Vocabulary: the paper's terms and the tool's names.** The tool and the Lean development
predate the paper's final vocabulary and keep their own names; this table is the map, and
the sections below use the paper's term with the tool's name in parentheses at first use.

| paper | tool / Lean |
|---|---|
| mode fact `I_m` of a mode (Definition 2; "mode invariant" until paper commit `780d237`) | the checked cut of the mode, its conjuncts the kept atoms: `OracleAPI.checkedCut` / `checkedCutX`, `EvolStrengthening(X)` (`InstancesV2/Cuts/<b>.lean`), the `cuts` of `regionG guard cuts`, `cutsOK`, the stay verdicts, `CutLiftX` |
| segments (Definition 3): joint and right-only, over one pair of modes | the certificate side: a joint segment's flow fact is a pack `Verd l q` (`modalVerdX`) at the pairing's stretch, a right-only segment's is a reposition pack `VerdD l q` (`modalVerdDynX`) plus a progress certificate; the tool's "windows" are the LEFT side's clock-capped cycles (`window_t`, `gwindowSeg`), one per left mode, which the segments of one strategy branch fill |
| witness strategy (Definition 4), the tree | the cover: `CoveredX` (`Checker/CoverX.lean`), the emitted record `CoverEmitE`, its walk `coverX_piece` |
| stretch `λ` (Lemma 1, Definition 5) | `lam l q` per pairing, `lamQ` per window, `lamN`/`lamD` in the records (the bridge instance replays the stretch of every pairing from the emitted cover); the segment span `δ = ε_R / λ` |
| flow certificate `flowC` (Definition 5) | a pack discharged by one of the three routes (A whole-domain, B boundary, C superlevel); `hbox`, `couple_box_cutX`, `couple_box_dyn` |
| non-connection certificate `nonC` (Definition 6); a pruned mode change | pruning: `NonConn.queries` (source and barrier checks), `nonconn_sound`, the `pruned` list of the cover, `SearchGraph.retainedSucc`; `RELCERT_NO_PRUNE=1` disables it |
| reposition certificate `repoC` (Definition 7) | the progress certificate: `Trusted/ProgressEmit.lean` (stages, rate / keep / land queries), `RepoProgress`, `repoProgress_*`, `progressVerd_*`, `relcert-progress-verdicts`; `RELCERT_NO_PROGRESS=1` disables it |
| landing set `S` of a segment (the children of a strategy node) | the retained successors `SearchGraph.retainedSucc` for the all-successors rules (`step`, `stepRepoPre/Post`), or the chosen set `S` of `stepChosen` / `repoChosen` |
| committed subset of the retained successors (Lemmas 3 and 4, Definition 8) | the existential mode choice ("choice"): `stepChosen`, `repoChosen` and the entry hop `hop`, their coverage certificates `hcovJ` / `hcovR` / `hcovS`, `Trusted/ChoiceEmit.lean`, the choice groups of `relcert-bridge-verdicts`; `RELCERT_NO_CHOICE=1` disables it |
| operating region `op_R` (the right can select a successor of its stored mode) | the mode-consistent region `regionG guard cuts q = guard q ∧ cuts q` of the right's current mode, carried in the loop invariant as `mvRegionR` |
| cover of a configuration `(m_R, B, σ)` (Definition 8) | `Config = ⟨q, B, SrcSetting⟩`, `decideCoveredX` (fuel-bounded), the budget `B = ⌈ε_L/δ⌉` |
| handoff condition (Eq. 13) | `Handoff.queryOf`, the hypothesis `hhand` of `theorem3_modeKeyed` |
| Theorem 3 (Soundness of Synthesis) | "Theorem 3" in every Lean docstring and in this file; `theorem3Form`, `theorem3_of_coverX`, `<b>_bridge` |

**Lean names.** The Lean names keep the development's vocabulary; the comments and
docstrings use the paper's numbering. `theorem3Form`, `theorem3_of_coverX` and the
`<b>_bridge` instances are the paper's Theorem 3; in this file "a benchmark's Theorem 3" or "a
Theorem 3 instance" names that Lean statement. The reposition certificate (Definition 7) is
the "progress certificate" (`ProgressEmit.lean`, `repoProgress_*`, `progressVerd_*`,
`RepoProgress`); the tool keeps the name "progress" too. The paper's `I_m` (a mode fact of
mode `m`, Definition 2: one per mode, `true` by default, fixed by preprocessing) is the tool's
checked cut, whose conjuncts are the kept atoms; the Lean names keep "cut" (`checkedCut`,
`EvolStrengthening`, `CutLiftX`, the stay verdicts), and the checked cut was in the Lean
development as the cut certificate (§2, §7) before the paper named it.
New in the paper, with no Lean statement of their own: Assumption 1 in Section 3
(with the remark that `next(q)` always serves as the exits of a joint segment; the operating region `op_R` and
the admissible initial modes are defined in Section 3), Definition 3 (Segments),
Definition 4 (Witness Strategy), Theorem 1 (Soundness of Witness Strategies), Lemma 3 (Joint
Segments) and Lemma 4 (Right-Only Segments); Definition 2 (Mode Fact) has one, the cut
certificate (§2). Theorem 1 is the cover induction `coverX_piece`
and Lemmas 3 and 4 are steps of it (§2.2 below), as the paper's Mechanization paragraph says.

**The claim, in one sentence.** For every benchmark of the suite, the paper's Theorem 3 at
the declared invariant (the Lean "Theorem 3") is a kernel-checked Lean theorem whose only
non-standard axiom is Z3's `unsat` (`z3_unsat_sound`), produced by one generic theorem
(`theorem3_of_coverX`) instantiated from the records the tool emits; and Assumption 1 of
every right model is a separate kernel theorem with no Z3 leaf.

## 0. Two routes to the same statement

Every suite benchmark has its Theorem 3 (the paper's Theorem 3) twice, with the same
conclusion shape:

| route | theorem per benchmark | how the proof is produced | status |
|---|---|---|---|
| **generic bridge** (the paper's route) | `InstancesV2/Bridge/<B>.lean`, `<b>_bridge` (all 50 suite benchmarks + 2 choice exhibits) | generated by `scripts/gen_bridge.py` from the emitted records; structural facts by `decide +kernel`, Assumption 1 transported from the benchmark's `WellFormedR` lemma and lifted by one coordinate (the right clock; instance dimension `bridgeDimV2 b` = the lemma's dimension + 1), every Z3 fact as one `Verdicts` hypothesis discharged by `relcert-bridge-verdicts` (4475 groups, unchanged by the padded coordinate: no query reads it) | `docs/BRIDGE.md`; axioms: standard three + `z3_unsat_sound` |
| standalone instances (the earlier route, archived 2026-10-22) | `InstancesV2/Modal/<B>.lean`, `Instances/*Guarded.lean`, `BatteryV2.lean` on branch `archive/legacy-2026-10` | hand-written per benchmark: an explicit response that replays the emitted cover, each flow fact a named pack `Verd l q` discharged by `relcert --run-verdicts-v2` (on that branch) | the per-benchmark findings of that route: `docs/GUARDED-SWITCHING.md`; what was archived and why: `docs/CLEANUP-SCOPE.md` (planning record, last present at commit 29663d8). The three `InstancesV2/Choice/General/` files that remain (`VehicleAccelCopy`, `VehicleHypercert`, `WatertankChoice`) hold only the exhibits' right models and Assumption 1 proofs, lifted by one dimension into their bridge instances (Theorem-3 parts retired 2026-10-21, 61d7389). |

The bridge is what the sentences of this map point at. The standalone route was the historical
evidence (its responses are explicit and readable; archived on branch `archive/legacy-2026-10` on
2026-10-22); its per-benchmark findings stay in `docs/GUARDED-SWITCHING.md` and
`docs/SUITE-REDESIGN.md`.

## 1. Section 2: the problem

| paper | Lean | where |
|---|---|---|
| the model (Eq. model-timed): modes with dynamics, evolve domain, guards, declared successors `next`, a clock | the parsed `PProblem` (`Trusted/Parse.lean`), one literal per benchmark (`InstancesV2/BenchIR/<b>.lean`, re-parsed and compared by `relcert-test`); the search graph `SearchGraph` of right modes and edges, the left automaton `LeftAut` | `Trusted/Parse.lean`, `Checker/Cover.lean`, `Proofs/Encoding/ModeHandoff.lean` |
| the two-system program `(L, R)` of the relational formulation: the left runs its guard-gated program, the right responds | `theorem3Form L R Φ = Φ → [|(L*, R*)⟩⟩ Φ` with `L = leftAutomatonBody A u_L` (jump then flow: `?(u_L = m') ; ⋃_{t ∈ next m'} ?guard_t ; u_L := t ; window_t`) and `R = rightAutomatonBody Gr mv` (flow then jump: `?(mv = q) ; flow_q ; ⋃_e ?e.guard ; mv := e.tgt`); the ∀∃ modality is dL-rel's, bridged by `RFormula.encoding_correct` | `Checker/Cover/Encoding.lean`, `Proofs/Encoding/ModeHandoff.lean`, `Proofs/Encoding/JointBridge.lean` |
| **Definition 1** (∀∃ relational invariance): `φInv → [|(L,R)⟩⟩ φInv` | `RFormula.rvalid (theorem3Form L R Ψ)`, the conclusion of every Theorem 3 instance | `Checker/Cover/Encoding.lean` |
| Eq. (relational-invariant), Eq. (mode-inv): one iteration, per left mode | the per-window step `GResp` (one left window, the right's guarded response) and its assembly into the loop | `Proofs/Encoding/GuardedSwitch.lean`, `EnvelopeChainR.lean` |
| Eq. (polynomial-invariant): `φInv` a conjunction of polynomial inequalities `g_i ≤ 0` | `canonInvM g gs` (the list of components as one canonical formula; its encoding theorem `encode_canonInv`) | `Proofs/Encoding/CanonicalInv.lean`, `EnvelopeChainM.lean` |
| Eq. (mode-dependent-inv-global): `Φ = ⋀_m (u_L = m → φ_inv(m))` | `psiK u_L ϕ nL domL domR BkR`: the rows keyed by `u_L`, both envelopes, the right bookkeeping, `u_L ∈ modes` | `Proofs/Encoding/ModeHandoff.lean` |

What the mechanized loop invariant carries beyond `φInv`: the evolve envelope `envLR` of both
sides and the right's **mode-consistent region** `regionG guard cuts q = guard q ∧ cuts q`
(the guard of the right's current mode and that mode's checked cuts, the paper's mode
facts `I_m` of Definition 2; the paper's operating region `op_R`), bookkeeping that the
flow-then-jump rotation maintains at every loop boundary.
This is the `(φInv ∧ op_R) → [|(L,R)⟩⟩ (φInv ∧ op_R)` form of the paper's Theorem 3.

## 2. Section 3: mode facts (the tool's checked cuts), segments, witness strategies, Assumption 1, composition

| paper | Lean | where |
|---|---|---|
| the run-time reading of a witness strategy: for each left window a chain of right segments (joint, right-only, and switches), chosen after the left run | `GResp G q P post σ` (the segments are chosen after the left run; the final successor at the end state) and the chain lemmas `RResp`/`RRespP` | `Proofs/Encoding/GuardedSwitch.lean`, `GuardedClimb.lean` |
| the operating region `op_R` and the admissible initial modes (Section 3) | the right's mode-consistent region `regionG guard cuts q` (§1) and `AdmissibleStart` (§6.1) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Anchor.lean` |
| a reposition (the right moves alone, the left frozen) | the right-only steps of `CoveredX` (`stepRepoPre`, `stepRepoPost`), the frozen left in `couple_box_dyn` | `Checker/CoverX.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| every mode switch of the witness passes the entered mode's guard | `SwitchLegal e ω := Formula.sat e.guard ω`; a right run is a sequence of legal switches (`guarded_rights_bridge`); every edge of the instance's graph carries the lowered guard of the mode it enters (`grOf_guards` in the bridge, `Gr_guards` in each standalone instance) | `Proofs/Encoding/GuardedSwitch.lean`, `Proofs/Encoding/Emitted/Data.lean` |
| **Definition 2** (Mode Fact), the preprocessing phase: `F_m` is the flow of mode `m` (the continuous phase of Eq. 1); a formula `I_m` over the variables of `m` is a mode fact of `m` if `g_m → I_m` and `I_m → [F_m] I_m` are valid; it then holds throughout every cycle of `m`. Preprocessing fixes one `I_m` per mode (`true` by default), and every obligation about a pairing `(m_l, m_r)` assumes `φ_inv(m_l)` together with the mode facts `I_{m_l} ∧ I_{m_r}` | the tool's checked cut, the cut certificate: per kept atom the entry check O1 (implied by the mode's guard, `g_m → I_m`) and the preservation check O2 (kept by the mode's own flow, `I_m → [F_m] I_m`, by one of the three routes of §3), found by `OracleAPI.checkedCut` / `checkedCutX` (untrusted), recorded as `EvolStrengthening` / `EvolStrengtheningX` (`InstancesV2/Cuts/<b>.lean`, well formed by `cutsOK_wfX`), O2 re-sent as the stay verdicts (`Bridge.stayQueryOf`, `atomsStayC_L/R`), and lifted to "holds along every run of the mode" by `Proofs/Soundness/CutLiftX.lean`; the kept atoms (the conjuncts of `I_m`) of both modes of a pairing are part of the anchor (§2.2, §7), which is how the strengthened invariant enters every obligation | `Trusted/OracleAPI.lean`, `Checker/EvolStrengthening.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean`, `Emitted/Stay.lean` |
| **Definition 3** (Segments): `seg^σ_joint(m_l, m_r, τ, S)` and `seg^σ_r-only(m_r, S)` in a source setting `σ`, from the entry states `entry(m_r) ∧ γ_σ` (`γ_pre-j = g_{m_l}`, `γ_post-j = true`) | no Lean definition of its own; the two segment obligations are what the joint and right-only cases of `coverX_piece` establish, §2.2 below; the setting is the `pre` flag of the configuration, and the pre-joint premise `γ_σ` is `(pre = true → Formula.sat gL y)` in `RepoProgress` | `Proofs/Encoding/CoverResp.lean` |
| **Definition 4** (Witness Strategy): a finite tree of right modes labelled with segments, rooted at an initial right mode `q₀` | the tree is the cover `CoveredX` walked by `coverX_piece`, §2.2 below | `Checker/CoverX.lean`, `Proofs/Encoding/CoverResp.lean` |
| **Assumption 1** (Well-Formedness), with the remark that `next(q)` always serves as the exits of a joint segment | `WellFormedR`, §2.1 below; adequacy of `next(q)` is clause (ii) | `Proofs/Encoding/WellFormedR.lean` |
| **Theorem 1** (Soundness of Witness Strategies): witness strategies for every admissible initial mode of every left mode, with the handoff condition Eq. 13 (`eq:handoff`) at left mode changes, give the forall-exists invariance within op_R; the left cycle case is the per-mode obligation Eq. 12 (`eq:mode-str`, the strengthened `str(φ_inv(m_l))` kept by one cycle of `m_l` against `R`) | the cover induction `coverX_piece` and its window assembly, §2.2 below; no standalone ∀∃ statement | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| **Theorem 2** (Composition): the per-mode strategies of Theorem 1 for every left mode, plus the handoff condition Eq. 13 (`eq:handoff`) at every declared left mode change, give the forall-exists invariance within op_R and the stored modes' domains (paper adds `D_{u_l} ∧ D_u` to pre- and postcondition, 2026-10-18; Lean's loop invariant `psiK` carries the envelope `envLR domL domR` from the start, `ModeHandoff.lean:185`, and the first iteration performs a handoff) | `theorem3_modeKeyed` (Proofs/Encoding/ModeHandoff.lean:360): the mode-keyed assembly with the conditioned handoff hypothesis; the paper's Theorem 3 (synthesis) instantiates it with covers | Proofs/Encoding/ModeHandoff.lean |

### 2.1 Assumption 1 (well-formedness)

| paper | Lean | where |
|---|---|---|
| **Assumption 1**: the right model is nonblocking and complete with respect to its declared successors: from every state in a source-mode guard an evolution spanning `ε_R` exists, and every evolution of duration at most `ε_R`, the empty one included, ends in the guard of a declared successor | `WellFormedR G guard ε`: for every mode `q` and state `x` in `q`'s lowered guard and evolve domain, (i) `∃ Φ, ODESol m.sys m.dom x ε Φ`, (ii) every run of duration `t ≤ ε` ends in `guard e.tgt` for some `e ∈ G.edgesFrom q` (the self-loop included); `G` the benchmark's guarded right automaton, `ε` the file's `epsilon` | `Proofs/Encoding/WellFormedR.lean` |
| its use in Theorem 3 | the hypothesis `hwf` of `theorem3_of_coverX`, `theorem3_keyed_of_records` (`Emitted/Keyed.lean:427`) and `theorem3_window_of_records` (`Emitted/Window.lean:83`) (stated as `WellFormedRIn G guard reg ε`, Assumption 1 relative to a right-only region `reg` kept by the right flows; every instance takes `reg = ⊤`, the paper's form) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Region.lean` |
| verified, not assumed, per benchmark | `<ns>.<b>_wellFormedR` for all 50 right models, Z3-free (the three standard axioms), audited on every build by `InstancesV2/WellFormedBattery.lean`; transported onto the bridge's graph by `wellFormedR_transport` (same modes, every standalone edge a declared successor, decided), or stated over that graph directly (`<b>_wellFormedR_direct`, the two dRL benchmarks and `freedm_meter`); then lifted by one coordinate, from the lemma's dimension `n0` to the bridge dimension `n0 + 1` (the right clock), by `wellFormedR_lift` (`Emitted/Lift.lean:292`) under the kernel-decided bundle `padOK IR n0` (`Lift.lean:108`: every right guard and evolve domain lowers at `n0 + 1` to the embedding of its lowering at `n0`, and the dynamics pad with the new coordinate frozen) | `InstancesV2/WellFormed/` (all 50, the 19 carried-over proofs included since 2026-10-22), `Emitted/Transport.lean`, `Emitted/Lift.lean`; `docs/WELLFORMED.md` §6 |
| the remark (self-loop whose guard contains the one-interval reach set, or a successor covering the rest) | the proof styles: (a) forward invariance of the guard then the self-loop, (b) exit into a successor's guard within one interval | `docs/WELLFORMED.md` §2 |
| the tool's sufficient check | `relcert --wellformed`: both clauses per right mode (clause (ii) as `ok (invariant)` / `ok (exit→S)`; clause (i), since 2026-10-26, from every guard state the flow stays in the evolve domain for `ε_R` and does not blow up; else `UNKNOWN`, or `BLOCKING` when a guard state leaves the domain at once), strict in `--check-quick-v2` (155 modes, 0 `UNKNOWN`, 0 `BLOCKING`); not part of the guarantee, which takes `WellFormedR` | `Trusted/WellFormedCheck.lean`, `docs/WELLFORMED.md` §4 |
| the six satellites | since 2026-10-15 their right evolve domains carry the conserved momentum band (total angular momentum about each wheel axis within the wheel's capacity), and Assumption 1 holds literally; before, it was proved on that band only | `docs/WELLFORMED.md` §3, `docs/SUITE-REDESIGN.md` §19.2 |

### 2.2 Definition 3 (segments), Definition 4 (witness strategy), Theorem 1 (soundness of witness strategies), Lemma 3 and Lemma 4

The paper states two segment obligations (Definition 3), assembles them into a witness
strategy (Definition 4, a finite tree), and derives each obligation from a certificate: Lemma
3 (Joint Segments, Section 4.2) gives `seg_joint(m_l, m_r, min(ε_l, ε_r/λ))` from
`flowC(m_l, m_r, joint, λ)` through Assumption 1, Lemma 1 and the box; Lemma 4 (Right-Only
Segments, Section 4.3) gives `seg_r-only(m_r, ret(m_r))` from `flowC(m_l, m_r, right-only, ·)`
and `repoC(m_r)`, the retained successors as exits. Theorem 1 (Soundness of Witness
Strategies, Section 3) says that witness strategies for every admissible initial mode give the
per-mode obligation Eq. 12 (`eq:mode-str`) within `op_R`; its proof is a structural induction on the strategy tree with a per-node
budget (`ε_l` minus the joint durations above), splitting the left flow by autonomy at joint
nodes, which mirrors the induction on the `CoveredX` derivation in `coverX_piece`. In Lean none of the three statements is a standalone theorem with
the paper's ∀∃ statement: `theorem3_of_coverX` goes from the certificate facts to the matching
directly, Theorem 1 is its cover induction and Lemmas 3 and 4 are steps of it, as the paper's
Mechanization paragraph says.

| paper | Lean | where |
|---|---|---|
| the entry states of a segment: `φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r} ∧ m_r ∈ next(u)` (∧ `γ_σ` in setting σ; since 2026-10-18 the paper reads every guard together with its mode's domain, so `I_m` includes `D_m` and the left domain is no separate conjunct; the tool and Lean keep domains as a separate piece of the anchor, which is equivalent), where `I_{m_l}` is the mode fact of `m_l` fixed by preprocessing (Definition 2): the left is inside a cycle of `m_l`, where `I_{m_l}` and its domain hold, and the right may select `m_r` | (Lean: the anchor implies both domains, `hAdom : A q → domL ∧ domR`, `Progress.lean:579`; Lean's cycle starts after selection, `modeStep = ?(mv = q); ode_q; switch`, `JointBridge.lean:33`) | an anchor state `A l q` (`Emitted/Anchor.lean`): the row, the envelope, the guard of `q` and the kept atoms of both modes; the kept atoms of `m_l` are its checked cuts (the conjuncts of `I_{m_l}`), entered from the left guard (O1) and kept along the left flow (O2, the stay verdicts `atomsStayC_L`), which is how `I_{m_l}` holds at every entry state | `Proofs/Encoding/Emitted/Anchor.lean`, `Emitted/Stay.lean` |
| `seg_joint(m_l, m_r, τ)`: from the entry states `φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r}`, `[|(F_{m_l}^{≤τ}, R^{m_r})⟩⟩ I_{m_l}` (the flow of `m_l` for at most `τ`, timer started at 0; one right cycle) | the joint cases of `coverX_piece` (`CoverResp.lean:316`): the partial-span case is `coverX_finish` (`CoverResp.lean:243`), the full-span branch of `step` (`CoverResp.lean:347` to `394`) inlines the same reasoning | `Proofs/Encoding/CoverResp.lean` |
| **Lemma 3** (Proving Joint Segments, at the end of Section 4.2): `flowC(m_l, m_r, joint, λ)` gives, in every source setting σ, `seg^σ_joint(m_l, m_r, min(ε_l, ε_r/λ), ret^joint_σ(m_r))` | inside those cases: the right run of span `δ = ε_R/λ` exists by Assumption 1 clause (i); `joint_stretch` (`ReplayEngine.lean:117`) and the rescaling lemma `joint_of_sols_lam` (`SyncSwitch.lean:188`, the paper's Lemma 1) pair it with the left run as one run of the joint product program; the certificate (`hbox`) keeps the anchor along it; the end state enables a declared successor by clause (ii) | `Proofs/Encoding/CoverResp.lean`, `ReplayEngine.lean`, `SyncSwitch.lean` |
| `seg^σ_r-only(m_r, S)` for a landing set `S` of right modes: with the left frozen, from the same entry states `φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r} ∧ γ_σ`, the single formula `⟨R^{m_r}; R*⟩ (I_{m_l} ∧ land(S))`, a run of the right system starting with a cycle of `m_r`, with `land(S) = ⋁_{q' ∈ S} (g_{q'} ∧ q' ∈ next(u))` (since 2026-10-18; matches the general chain `RRespPC`, `ClockedRight.lean:226`, the clocked twin of `RRespP`, `GuardedClimb.lean:88`, which may pass through several modes, each cycle of duration `≤ ε_R`; `RepoProgress` is the single-mode instance Lemma 4 yields, at least one segment, possibly of zero duration, `land_at_start`, `Progress.lean:605`) (end state only; no intermediate state is constrained) | `RepoProgress G tr epsR …` (`CoverResp.lean:146`): from a reposition start, right-only clocked cycles of the node until a retained exit is enabled, the anchor holding at the switch state; through `RRespPC` (`ClockedRight.lean:226`) it constrains only the end state, exactly the paper's form; consumed by `repoStep` (`CoverResp.lean:276`) inside `coverX_piece`; `S` is the retained successor set | `Proofs/Encoding/CoverResp.lean` |
| **Lemma 4** (Proving Right-Only Segments): `flowC(m_l, m_r, right-only, ·)` and `repoC(m_r)` give `seg_r-only(m_r, ret(m_r))` | `repoProgress_one` (`Progress.lean:627`), `repoProgress_two` (`Progress.lean:659`), `repoProgress_one_down` (`Progress.lean:761`): the stage ladder, the right-only flow box (`hboxD`) and the right-only non-connection facts (`hpruneD`) prove `RepoProgress` (the paper's proof: the box keeps the invariant along every run, the reposition diamond picks one, which ends in both); discharged per benchmark by `hrepoProg_of` (`Emitted/Progress.lean:195`) and handed to `theorem3_of_coverX` as the `hrepoProg` field of `CoverHyps` | `Proofs/Encoding/Progress.lean`, `Emitted/Progress.lean` |
| **Definition 4** (Witness Strategy): a finite tree rooted at an initial right mode `q₀`, nodes right modes labelled with a segment in the node's setting σ (pre-joint iff no joint node above it); a joint node `q` carries `seg^σ_joint(m_l, q, τ_q, S)` and a right-only node `seg^σ_r-only(q, S)`; in both cases the children are exactly the landing set `S`; a joint node is a leaf when the `τ`'s on its branch sum to at least `ε_l` | the cover `CoveredX` (`Checker/CoverX.lean`) read as a tree: `step` is a joint node whose children are the retained successors, `stepRepoPre`/`stepRepoPost` a right-only node, `base` a leaf (the remaining budget fits one segment). The exit set is the retained successor set `retainedSucc` in the all-successors rule and the chosen set `S` of the choice rules (`stepChosen`, `repoChosen`), whose adequacy is the coverage certificate (`hcovJ`, `hcovR`, `hcovS` in `CoverHyps`, `docs/CHOICE-SOUNDNESS.md`) | `Checker/CoverX.lean`, `Proofs/Encoding/Theorem3General.lean` |
| **Theorem 1** (Soundness of Witness Strategies): witness strategies for every admissible `q₀` of every `m_l`, plus the handoff condition Eq. 13, give the forall-exists invariance within op_R (per left cycle: the per-mode obligation Eq. 12 for `m_l`); the proof splits the left execution by autonomy and walks the tree | `coverX_piece` (`CoverResp.lean:316`): the walk of the tree, one clocked left piece answered from a node of `CoveredX` (the segment runs, the anchor is kept, a child is entered legally, the budget decreases); `coverX_gresp` (`CoverResp.lean:521`) lifts it to `GResp` over one left window; the window assembly `Hmulti_of_coverX` (`Theorem3General.lean:131`) splits the left execution into windows and quantifies over the admissible starts | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| an older single-segment route (not used by `theorem3_of_coverX`) | `segment_faModal` (`Core/Reify.lean:100`) and `segment_relational` (`EncodingBridge.lean:53`): ∀∃ segment theorems with a carried duration-existence side condition | `Core/Reify.lean`, `Proofs/Encoding/EncodingBridge.lean` |

## 3. Section 4.1: flow certificates (Lemma 1, Definition 5, Lemma 2; Lemma 3 of Section 4.2) and the discharge of mode facts (Section 6.1, "Mode facts.")

| paper | Lean | where |
|---|---|---|
| the joint product program `α_joint^λ` (Eq. 14, `eq:joint-dynamic-stretched`): `ẋ_L = f_L`, `ẋ_R = λ f_R`, under both evolve domains | `Program.ode (jointSys fL fR (Term.const λ)) (domL ∧ domR)` | `Core/FlowCert.lean` |
| the right-only product program `α_right-only` (Eq. 15, `eq:rightonly-product`): left frozen | `rightBlock fR` with the left coordinates unmoved (`mergeLR`), the dynamic reposition program | `Proofs/Encoding/ReplayDyn.lean`, `RepoPrefixR.lean` |
| **Lemma 1** (Time Stretching): `φ` solves `ẋ = f` on `[0, λτ]` iff `s ↦ φ(λs)` solves `ẋ = λf` on `[0, τ]` | `sem_rightBlock_reparam`, `sem_rightBlock_reparam_iff`; the right projection of a joint run time-rescaled, `odeSol_right_of_joint`; the joint rescaling used by the cover induction, `joint_of_sols_lam` | `Proofs/Encoding/Reparam.lean`, `Emitted/Region.lean`, `SyncSwitch.lean` |
| Eqs. 16 to 18 (`eq:lie-condition`, `eq:boundary-preservation`, `eq:domain-preservation`): the Lie-derivative conditions over the domain and the mode facts `I_{m_l} ∧ I_{m_r}` (the tool's checked cuts; the tool's sufficient condition); the sentence after them, "Certification proceeds in rounds" (a differential cut: a component's condition may assume the components of earlier rounds) | the three query routes of one component: whole-domain `dom ∧ ġ > 0` (route A), boundary `dom ∧ g = 0 ∧ ġ ≥ 0` (route B), superlevel `dom ∧ g ≥ 0 ∧ ġ > 0` (route C), each `unsat`; the **pack** of a pairing `(l, q)` at its stretch: one `unsat` per component by any of the three routes, over the segment domain narrowed by the kept atoms (the checked cuts), in the strata order the tool recorded (`modalVerdXQueries`); the reposition pack `modalVerdDynXQueries` for the right-only kind | `Core/FlowCert.lean` (`flowQuery`, `flowQueryStrict`, `lieDeriv`, `tderiv_correct`), `Proofs/Flow/DISuperlevel.lean`, `Proofs/Flow/StratifiedBarrier.lean` (rounds), `VerdictsV2/ModalX.lean`, `ModalDynX.lean` |
| "Mode facts." (Section 6.1; the preprocessing phase of Section 3): the tool's preprocessing, its checked cuts, which find and discharge the mode facts `I_m` of Definition 2 | the cut certificate, the Definition 2 row of §2 (`OracleAPI.checkedCut` / `checkedCutX`, `EvolStrengthening(X)`, the stay verdicts, `CutLiftX`) | `Trusted/OracleAPI.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean` |
| **Definition 5** (Flow Certificate): `flowC(m_l, m_r, kind, λ)` holds if `entry(m_r) → [α_kind^λ] I_{m_l}` is valid (preservation from the entry states; since 2026-10-18 the paper drops the former items (1)/(2), the mode facts, which only the Lie-condition discharge uses and Lemma 2 assumes) | the mode facts: the cut certificates of the two modes (Definition 2, §2), premises of Lemma 2; the certificate itself: the box as the general theorem consumes it, the `hbox` field of `CoverHyps` (joint kind: the anchor kept along every run of the stretched joint flow from an anchor state, the anchor carrying both modes' kept atoms) and the hypothesis `hboxD` of the `repoProgress_*` lemmas (right-only kind: the anchor kept along the frozen-left flow); per segment `couple_box_cutX` (joint) and `couple_box_dyn` (right-only) | `Proofs/Encoding/Theorem3General.lean`, `Progress.lean`, `SyncSwitch.lean`, `ReplayDyn.lean` |
| **Lemma 2** (Lie Conditions): the conditions over the domain strengthened by `I_{m_l} ∧ I_{m_r}`, when both are mode facts, prove the box of Definition 5 | `flow_cert_sound` (one component: an `unsat` route query gives `BoxLe` along the stretched joint flow, through dL-lean's `DI_nonstrict_domain`); threaded over the components with the kept atoms by `check_sound_multi_cutX` | `Core/FlowCert.lean`, `Proofs/Soundness/CutLiftX.lean` |
| **Lemma 3** (Proving Joint Segments, at the end of Section 4.2): `flowC(m_l, m_r, joint, λ)` gives, in every source setting σ, `seg^σ_joint(m_l, m_r, min(ε_l, ε_r/λ), ret^joint_σ(m_r))` | a step of `coverX_piece`, §2.2 | `Proofs/Encoding/CoverResp.lean` |
| the tool's query, the runner's query and the theorem's hypothesis are the same formula | the runner rebuilds each query from the committed records with the tool's own lowering and printer; the bridge instance's `Verdicts` hypothesis is the runner's group list itself (`Emitted/Run.lean`, `verdicts_of_groups`), its stretches read from the emitted cover record; in the bridge, `Verdicts` is by definition the runner's group list (`Emitted.verdicts_of_groups`) | `VerdictsV2/`, `Proofs/Encoding/Emitted/Run.lean` |

Existence of the right flow for the needed duration is not part of Definition 5 or Lemma 2 in
the paper; Lemma 3 draws it from Assumption 1, and so does Lean (clause (i), §2.1), used by
the general theorem (the archived standalone instances used an explicit solution or a
viability argument, `Proofs/Flow/`).

## 4. Section 4.2: non-connection certificates (Definition 6)

| paper | Lean | where |
|---|---|---|
| the programs `β_joint` (one cycle of the right mode; the stretch is dropped by Lemma 1) and `β_right-only` | the right flow of the stretched joint program and the frozen-left flow, as under Definition 5 | `Core/FlowCert.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| **Definition 6** (Non-Connection Certificate): a non-connection certificate for `m_R → m_R'` proves `entry_σ(m_r) → [β_kind] ¬g_{m'}` (one display; guards read with their domains, so the former `C`/`N` with explicit domains collapse; the tool's query keeps the domains explicitly, which is equivalent) (no entry state of the target is reached) | the two checks as the tool sends them, `NonConn.queries` (source: no entry state of `m_R` satisfies the threshold guard; barrier: on the threshold the flow moves the variable away), defined once for the certifier, the runner and the kernel | `Trusted/NonConnQuery.lean` |
| the consequence sentence after Definition 6 (no numbered statement): the declared change is never taken under `(σ, kind)` | `nonconn_sound` (dL-lean `DI_strict` on the safe-side term); `nonconn_of_unsat`: the runner's two `unsat` answers are its hypotheses | `Checker/NonConn.lean`, `Proofs/Encoding/NonConnBridge.lean` |
| the remark that the retained successors `ret^κ_σ(q)` are the exits segments of kind κ reach (Assumption 1 enables a declared successor at a segment end; a pruned one would be a connecting state); where a pruned edge leaves the cover | `SearchGraph.retainedSucc` (`Checker/Cover.lean:100`) drops it; the cover record carries the `pruned` list the kernel replays; in `coverX_piece` the end state of a joint segment enables a declared successor (Assumption 1 clause (ii)) whose guard is excluded for every pruned exit (`guard_pos_of_barrier`), so the retained set still serves as the exit set | `Checker/Cover.lean`, `Checker/CoverX.lean`, `Proofs/Encoding/Emitted/Barrier.lean` |
| where it enters Theorem 3 | the bridge keeps the barrier term of every pruned exit of the current right mode in the anchor: `≤ 0` on entry (source check), kept along joint and frozen flows (barrier check), `> 0` under the target's guard, so the target's guard never holds at a segment end (`nonconn_entry`, `nonconn_keep`, `guard_pos_of_barrier`; the general theorem's `hprune` field of `CoverHyps`, and `hpruneD` of the `repoProgress_*` lemmas for the right-only kind) | `Proofs/Encoding/Emitted/Barrier.lean` |
| suite | 46 pruned edges, both queries of each discharged (`--check-quick-v2`, and as groups of `relcert-bridge-verdicts`); the per-edge standalone instance `match_multi_rate_nonconn` for `DRIVE → STALL` is archived on branch `archive/legacy-2026-10` | `Checker/NonConn.lean`, `Trusted/NonConnQuery.lean`, `Proofs/Encoding/NonConnBridge.lean` |

## 5. Section 4.3: reposition certificates (Definition 7, Lemma 4; the stage lists of Section 6.1)

The paper calls them reposition certificates; the tool and Lean call them progress
certificates (`Trusted/ProgressEmit.lean`, `Proofs/Encoding/Progress.lean`,
`VerdictsV2/ProgressPin.lean`, `relcert-progress-verdicts`).

| paper | Lean | where |
|---|---|---|
| the region of the stage-ladder queries, `R ≡ I_{m_l} ∧ I_{m_r} ∧ φ_inv(m_l)` (the mode facts of both modes (the tool's checked cuts) and the invariant; defined in Section 6.1, "Reposition."; the tool's region adds the right evolve domain); retained successors `ret(q)` = declared, non-self, not pruned by a non-connection certificate | the node's region (the anchor `A q`, its kept atoms, the right domain); `retainedSucc` | `Checker/Cover.lean`, `Emitted/Anchor.lean` |
| **Definition 7** (Reposition Certificate; the tool's progress certificate): with the mode facts `I_{m_l}` of `m_l` and `I_{m_r}` of `m_r` (Definition 2), `repoC^σ(m_r)` is a proof that `entry^σ(m_r) → ⟨R^{m_r}; (R^{m_r})*⟩ land(ret_σ(m_r))` is valid, `entry^σ(m_r) = φ_inv(m_l) ∧ I_{m_l} ∧ g_{m_r} ∧ m_r ∈ next(u_r) ∧ γ_σ` | the conclusion of the `repoProgress_*` lemmas, `RepoProgress` (`CoverResp.lean:146`): from a reposition start, cycles of the node until a retained exit is enabled, the anchor kept | `Proofs/Encoding/CoverResp.lean` |
| the stage ladder (the rate, keep and landing obligations (stated in prose in Section 4.3), rate / keep / land), the tool's sufficient condition | per reposition node: staged rate bounds (`rateQuery`), kept thresholds (`keepQuery`) and the landing (`landQueries`: on the crossing line and at an already-crossed start some exit's guard holds); emitted by default (`RELCERT_NO_PROGRESS=1` disables it) | `Trusted/ProgressEmit.lean` |
| the progress-function argument (Section 6.1, no numbered lemma): with the right-only flow certificate, the ladder implies `repoC^σ` with the cycle bound `Σ ⌈d_i/(r_i ε_r)⌉` (d_i the remaining distance) | (hypotheses include the right-only flow box `hboxD` and `hpruneD`, `Progress.lean:572-601`) | `repoProgress_one` (`Progress.lean:627`), `repoProgress_one_down` (`Progress.lean:761`, a single downward stage) and `repoProgress_two` (`Progress.lean:659`), standard axioms; `progressVerd_one/one_down/two` (`VerdictsV2/ProgressPin.lean`) read the runner's `unsat` answers as its facts | `Proofs/Encoding/Progress.lean`, `VerdictsV2/ProgressPin.lean` |
| **Lemma 4** (Proving Right-Only Segments): `flowC(m_l, m_r, right-only, ·)` and `repoC(m_r)` give `seg_r-only(m_r, ret(m_r))`, the retained successors as exits | a step of `coverX_piece`, §2.2: `hrepoProg_of` (`Emitted/Progress.lean:195`) folds the ladder facts, the right-only flow box `hboxD` and the right-only non-connection facts `hpruneD` into `RepoProgress`, the `hrepoProg` field of `CoverHyps`, consumed by `repoStep` | `Proofs/Encoding/Emitted/Progress.lean`, `CoverResp.lean` |
| suite | 147 certificates, all discharged (`relcert-progress-verdicts`) | `docs/THEOREM3-GENERAL.md` §3 |

Why the premise is needed: the proof sketch of the synthesis theorem says Assumption 1
"continues every segment along a retained edge". For a right-only segment that is not enough:
Assumption 1 may enable only the self-loop, the right-only case of Definition 8 needs a non-self
exit, and nothing in Definition 5 says one is reached. The general theorem therefore takes
`hrepoProg : RepoProgress …`, which the reposition certificate discharges.

## 6. Section 5: the cover and Theorem 3

### 6.1 Definition 8 (cover)

| paper | Lean | where |
|---|---|---|
| configuration `(m_R, B, σ)` with budget `B` and source setting `σ ∈ {pre-joint, post-joint}` | `Config = ⟨q, B, SrcSetting⟩`, `B : ℕ` segments (the budget `⌈ε_L/δ⌉`, `δ = ε_R/λ` the common span) | `Checker/Cover.lean` |
| weights: the certified segment durations `τ_{m_r} = min(ε_l, ε_r/λ)`; node kinds from Lemma 3 (joint) and Lemma 4 (right-only) | the segment span `δ` of the pairing's stretch, `B` segments per window; the cover flags `jointOK` and `dynPre`/`dynPost` | `Checker/CoverEmit.lean`, `Emitted/Data.lean` |
| **Lemma 5** (Covers Are Witness Strategies): a cover from `(q₀, ε_l, pre-joint)`, viewed as a tree, is a witness strategy (Definition 4): children = the retained successors of the node's kind, `ret^κ_σ(q)`, the exits of Lemmas 3 and 4 | no separate reading: `coverX_piece` walks `CoveredX` directly (§2.2); the retained successor set `SearchGraph.retainedSucc` is the landing set of a joint node, the exits of a right-only node are the retained exits of `RepoProgress`; for the choice rules the chosen set `S` is the exit set certified by its coverage certificate (`hcovJ`, `hcovR`, `hcovS`) | `Proofs/Encoding/CoverResp.lean`, `Checker/Cover.lean` |
| finish case: a prefix of the certified joint segment finishes the left cycle | `CoveredX.base` | `Checker/CoverX.lean` |
| continue case, joint kind: every retained successor covered at `B − w` with `σ' = post-joint` | `CoveredX.step` | |
| continue case, right-only kind: every retained exit covered, `σ` unchanged | `CoveredX.stepRepoPre`, `stepRepoPost` | |
| continue case, committed subset: every target of a committed subset covered, the segment certified with that subset as landing set | `CoveredX.stepChosen` (joint), `repoChosen` (right-only), `hop` (`Checker/CoverX.lean:72-89`); the landing set from the coverage verdicts `hcovJ`/`hcovR`/`hcovS` (`CoverResp.lean:197-207`, region implies some guard of the subset) | `Checker/CoverX.lean`, `Proofs/Encoding/CoverResp.lean` |
| "only configurations reached by finitely many applications" | `CoveredX` is inductive; the checker `decideCoveredX` is fuel-bounded (`fuelOf`); `decideCoveredX_sound` says an accepted configuration is covered | `Checker/CoverX.lean` |
| the search graph: certified kinds, weights, retained edges | the emitted cover record `CoverEmitE` (flags per node: `jointOK`, `dynPre`/`dynPost`; stretches; pruned edges; admissible starts; strata orders) replayed in the kernel: `coversOK` (bridge, `decide +kernel`) | `Checker/CoverEmit.lean`, `Emitted/Keyed.lean` |
| admissible initial right mode `q₀` for `m_L` | `AdmissibleStart gL φ env (guard q) (cuts q)`: some joint state in the left guard, the invariant, the envelope and the right region; the dropped starts are those whose admissibility query is `unsat` (`Bridge.admQueryOf`, `adm_sound`) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Barrier.lean` |
| the tool's cover (Section 6.1) | `OracleAPI.certifyWithData`: the same recursion over configurations, untrusted; its output is replayed as above | `Trusted/OracleAPI.lean` |

Two more cases, `stepChosen`, `repoChosen` and `hop`, are the existential mode choice (a
subset of successors with a coverage certificate, an entry hop). It is the tool's default
(`RELCERT_NO_CHOICE=1` disables it; one sentence in the paper's Section 6.1), vacuous for the 46
original benchmarks (their covers are byte-identical with the feature on and off) and needed by
the four literature benchmarks (`drl_car_stop`, `drl_lane_control`, `vehicle_hypercert`,
`freedm_meter`: the right commits to the left's mode, or to a zero-net grid mode) and the two exhibits of `benchmarks/choice/`;
`docs/CHOICE-SOUNDNESS.md`.

### 6.2 Theorem 3 (soundness of synthesis)

> `str(φInv) → [|(L*,R*)⟩⟩ str(φInv)` (Eq. 10, `eq:strengthening`, `str(φ) ≡ φ ∧ op_R ∧ Q_{u_l} ∧ Q_{u_r}`) if (1) `R` satisfies Assumption 1; (2) for every
> `m_L` every admissible `q₀` admits a cover from `(q₀, ε_L, pre-joint)` at
> `φ_inv(m_L)`; (3) every declared left mode change satisfies the handoff condition
> (Eq. 13, `eq:handoff`).

Mechanized as `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean:183`, standard axioms
only; the Z3 axiom enters only through the instances' verdict hypotheses). Its right program is
the clocked automaton `rightAutomatonBodyC Gr (Aux, a) (Aux, d) epsR` (§9: each cycle flows for
at most `ε_R`, the cap as a post-test); the right clock `tr = (Aux, d)` is a parameter of
`CoverHyps` (`Theorem3General.lean:42`) and of `RepoProgress G tr epsR …` (`CoverResp.lean:146`),
whose responses are the clocked relation `RRespPC` (`ClockedRight.lean:226`); the only hygiene
facts are `tr ∉ range Lv` and `tr ∉ range Rv` (`CoverResp.lean:160`). The paper proves
Theorem 3 by Theorem 2 (Composition), which applies Theorem 1 (Soundness of Witness Strategies) per left cycle and the handoff condition at left mode changes. The
paper's Mechanization paragraph: the Lean theorem goes from the certificate facts to the
matching directly; Theorem 1 is its cover induction and Lemmas 3 and 4 are steps of it, none a
standalone statement (§2.2).

| paper condition | Lean hypothesis | discharged in an instance by |
|---|---|---|
| (1) Assumption 1 | `hwf : WellFormedRIn Gr guard reg epsR` | the benchmark's `WellFormedR` lemma (§2.1) at its own dimension `n0`, transported onto the pruned graph (`wellFormedR_transport`) and lifted to the instance dimension `n0 + 1` by `wellFormedR_lift` (`Emitted/Lift.lean:292`) under the decided bundle `pad_ok : padOK IR n0 = true` (`decide +kernel`) |
| (2) the covers, per `m_L` and admissible `q₀` | `hcov : ∀ l q, AdmissibleStart … → CoveredX Gr (ch l) ⟨q, B l, preJ⟩`, with `hdt : dt ≤ B l · δ l` (the window fits the budget) | covered starts by `decideCoveredX` on the emitted record (`coversOK`), the other starts inadmissible by their `unsat` (`adm_sound`) |
| (2), what each cover step consumes (Definitions 5, 6 and 7, and the segment-level facts) | `H : ∀ l, CoverHyps …` (`Theorem3General.lean:42` to `73`), whose fields are: the flow certificate of every certified joint pairing at its stretch (`hbox`); the non-connection certificates of the pruned edges (`hprune`); the entry condition (`hhand`: the anchor of `q` and the guard of `q'` give the anchor of `q'`); the reposition-progress premise (`hrepoProg : RepoProgress …`, §5); the coverage certificates of chosen sets (`hcovJ/R/S` with their regions `hRJ/RR/RS`, vacuous for the suite); and the side conditions `hlam`, `hspan`, `hAfv`, `hAdom`. The right-only flow box (`hboxD`) and the right-only non-connection fact (`hpruneD`) are not fields: they are hypotheses of the `repoProgress_*` lemmas (`Progress.lean:589`, `:592`) and are folded into `RepoProgress` when it is discharged | the bridge's `coverHyps_of` from the `Verdicts` structure (`Emitted/Keyed.lean`); `hrepoProg` by `hrepoProg_of` (`Emitted/Progress.lean:195`) |
| the loop invariant's right bookkeeping (`op_R`) | the anchor `A l q` (`hAstart`, `hApost`): the row, the kept atoms of both modes, the barrier terms of `q`'s pruned exits, the envelope; its region part `regionG guard cuts q` | `Emitted/Anchor.lean` (`AG`, `AG_start`, `AG_post`) |
| (3) the handoff condition (Eq. 13, `eq:handoff`): `φ_inv(m_L) ∧ dom_{m_L} ∧ guard_{m_L'} ∧ dom_{m_R} → φ_inv(m_L'), for a change from m_L to a successor m_L' ∈ next(m_L)` | for mode-dependent rows, the hypothesis `hhand` of `theorem3_modeKeyed`; the runner's query `Handoff.queryOf` is exactly this implication with the declared domains conjoined (`handoff_of_unsat`, `handoff_sound`) | `Proofs/Encoding/ModeHandoff.lean`, `Trusted/Handoff.lean`, `Emitted/Barrier.lean` |
| the conclusion | `rvalid (theorem3Form (bigChoice (leftProgsOf …)) (rightAutomatonBodyC Gr (Aux, a) (Aux, d) (epsR p)) ((canonInvM g gs ∧ envLR domL domR) ∧ mvRegionR (Aux, a) (regionG guard cuts) …))`: one declared row (`windowClaim p n cX cov reg a b d dt`, `Window.lean:51`); for per-mode rows the composition through `theorem3_modeKeyed_gen` (`ClockedKeyed.lean:170`) over `leftAutomatonBody` with `psiK` (`keyedClaim p n cX cov reg a b c d dt`, `Keyed.lean:416`) | `Emitted/Window.lean`, `Emitted/Keyed.lean` |
| the per-benchmark theorem, mode-keyed form | `theorem3_keyed_of_records (hv : Verdicts p n cX cov prog ce) (hpo : progOK …) (hcovers : coversOK …) (hregR : reg.fv ⊆ range Rv) (hinv : RegionInvariant …) (hwf : WellFormedRIn (grOf p n (prunedOf cov)) (guardR p n) reg (epsR p)) (a b c d : Fin n) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) (dt : ℝ) (hdt : dt ≤ epsL p) : keyedClaim p n cX cov reg a b c d dt` (`Keyed.lean:427`); the generated instances take `a b c d = 0 1 2 3` and `reg = ⊤` | `Emitted/Keyed.lean`; `InstancesV2/Bridge/<B>.lean` |
| the per-benchmark theorem, window form | `theorem3_window_of_records … (hwf : WellFormedRIn …) (hsame : rowsSame p = true) (a b d : Fin n) (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (dt : ℝ) (hdt : dt ≤ epsL p) : windowClaim p n cX cov reg a b d dt` (`Window.lean:83`); the generated instances take `a b d = 0 1 2` | `Emitted/Window.lean` |
| the proof: Theorem 1 (Soundness of Witness Strategies) on the cover read as a witness strategy, plus the handoff condition | `coverX_piece` (`CoverResp.lean:316`): per case of `CoveredX`, the segment runs (Assumption 1 clause (i)), the anchor is preserved (Definition 5), the end state enables a declared successor (clause (ii)) that is not pruned (Definition 6), the switch is legal and the entered anchor holds (`hhand`); the budget decreases; the joint cases are the paper's Lemma 3 and the right-only cases (`repoStep`, from `RepoProgress`) its Lemma 4; `coverX_gresp` and `Hmulti_of_coverX` assemble the windows (Theorem 1); the handoff condition enters through `theorem3_modeKeyed` | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean`; `docs/THEOREM3-GENERAL.md` §2 |

The mode-dependent case (the paper's twelve benchmarks): `theorem3_modeKeyed_gen`
(`ClockedKeyed.lean:170`, the clocked twin of `ModeHandoff.theorem3_modeKeyed`) composes the
per-mode window responses with the handoff condition and the side conditions on `u_L`
(freshness, footprints; `sides_disjoint4` for the four auxiliary coordinates); the bridge
supplies the per-mode responses through `hstepMode_GRC` and `HMode_regionGC`
(`ClockedKeyed.lean:149`, `:129`). Mode-independent rows take the window form directly
(`rowsSame` decided).

## 7. Section 6: implementation and evaluation

| paper | Lean / tool | where |
|---|---|---|
| "a Lean 4 executable; its search is untrusted and only proposes; every cover it proposes is replayed by a kernel-verified checker; a small trusted layer parses, lowers, prints and talks to Z3" | `relcert` (`Main.lean`); the trusted surface, file by file, in `RelCertifier/Trusted/README.md`: parser (`Parse.lean`, `KeyAudit.lean`), lowering (`Run.lean`, `JointVars.lean`, `InvComponents.lean`, the query builders `Handoff.lean`, `NonConnQuery.lean`, `BridgeQueries.lean`, `ProgressEmit.lean`, `ChoiceEmit.lean`), printer (`Smt.lean`), Z3 (`Z3.lean`, `Oracle.lean` with the axiom), the untrusted certifier `OracleAPI.lean` | `RelCertifier/Trusted/` |
| flow certificates and the stretch: three routes per component; one stretch per left mode, else a stretch per pairing with the common span `ε_R/λ̂` | the routes as in §3; the stretch per pairing `lam l q`, the common span `δ l = ε_R / lamQ l`, the budget `⌈ε_L/δ⌉` (`Emitted/Data.lean`); the stretch of every pairing read from the emitted cover record by the bridge instance | `Trusted/OracleAPI.lean`, `Emitted/Data.lean` |
| non-connection pruning (threshold guards, two checks) | §4 | |
| reposition certificates (the tool's progress certificates) | §5 | |
| handoff check (negation of Eq. 13, `eq:handoff`, `unsat`, issued and counted for every declared left transition) | `Handoff.queryOf`; 187 transitions over the suite, all `unsat` (`docs/HANDOFF.md`) | `Trusted/Handoff.lean` |
| the cover and its budget (depth-first recursion, budget-neutral cycles rejected) | §6.1; `decideCoveredX` with fuel is the kernel's replay of the same recursion | `Checker/CoverX.lean` |
| checked cuts (the paper's mode facts, Definition 2 in Section 3, and "Mode facts." in Section 6.1; §2: the atoms implied by a mode's guard and preserved by its own flow narrow the segment domain; the `I_{m_l} ∧ I_{m_r}` of Eqs. 16 to 18 and of `R_q`) | O1 (entry) and O2 (invariance) per kept atom; the extended certificate `EvolStrengtheningX` kernel-checked well formed (`InstancesV2/Cuts/<b>.lean`, `cutsOK_wfX`); O2 in the bridge as the stay verdicts by the certificate's route (`Bridge.stayQueryOf`, `atomsStayC_L/R`); the lift `Proofs/Soundness/CutLiftX.lean` | `Checker/EvolStrengtheningX.lean`, `Emitted/Stay.lean` |
| "Mechanization" paragraph: a kernel-checked theorem per benchmark over the guard-gated programs; Z3 hypotheses tied to the exact queries; trust base = parser, lowering, printer, Z3 `unsat`, kernel; thirteen mode-dependent benchmarks composed with handoffs; Assumption 1 proved per benchmark; Theorem 1 (Soundness of Witness Strategies) as the cover induction, Lemmas 3 and 4 as steps of it, none a standalone statement | §0 (both routes), §6.2, §2.1, §2.2. Counts to quote (2026-10-27, after batch I6): 50 benchmarks (46 designed, 4 from the literature); bridge verdicts 4864 groups over the 52 instances (`relcert-bridge-verdicts`, the number Appendix B quotes), 4728 over the suite; handoff 517; non-connection 46 over 23 pruned edges; progress 107; Assumption 1: 50 of 50 | `STATUS.md` (`docs/VERDICTS.md` is archived on branch `archive/legacy-2026-10`) |
| Table 1 (`tab:benchmarks`, the suite by group), Table 2 (`tab:ladder`, the refinement ladder, Section 6.4) and the mechanism matrix | `scripts/suite_v2_matrix.py`, `scripts/paper_numbers.sh` (the frozen numbers the paper quotes) | `docs/SUITE-REDESIGN.md` |

**Paper text, checked against the submission.** The Mechanization paragraph (Section 6)
takes the certificates, the handoff conditions and Assumption 1 as hypotheses of one Lean
theorem over the programs of Eq. 1, says Assumption 1 is proved per benchmark without Z3, and
names the trust base (parser and lowering, query printer, Z3 `unsat`, kernel); Appendix B gives
the details and quotes the 3025 bridge groups over the 37 instances. The reposition certificate
is described in Section 4.3 and, as the tool's stage lists, in Section 6.1.

## 8. Where the numbers come from

| number | source |
|---|---|
| 50 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1` (15 need the existential mode choice, the default) | `scripts/paper_numbers.sh` (frozen), `benchmarks/suite_v2/` |
| 52 bridge instances, 4836 verdict groups (4700 over the 50 suite benchmarks, 136 over the 2 exhibits) | `InstancesV2/Bridge.lean`, `relcert-bridge-verdicts`, `expectedBridgeGroupsV2` |
| 50 Assumption 1 proofs, Z3-free; 83 kernel refutations, 241 verdict groups | `InstancesV2/WellFormedBattery.lean`; `InstancesV2/Refute.lean`, `relcert-refute-verdicts` |
| 26 pruned edges, 52 non-connection queries; 493 handoff queries; 147 progress (reposition certificate) queries | the same runner; `relcert-progress-verdicts` |
| Assumption 1: 50 of 50, Z3-free | `InstancesV2/WellFormedBattery.lean` |
| axioms of every instance: `propext`, `Classical.choice`, `Quot.sound`, `z3_unsat_sound` | `lake build … 2>&1 | grep -A3 "depends on axioms"`; `docs/CERTIFICATION-CHECK.md` check 2 |

## 9. Modelling choices to state in the paper

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `u_L`, clock | `leftAutomatonBody` with the lowered left guards, the declared `next` lists and `u_L`, windows clock-capped (mode-independent rows through `bigChoice` of the windows, carried by `theorem3_leftAut_of_choice`) | exact (jump then flow, as the paper writes it) |
| `?guard_m(x)` on right transitions | every edge carries `hostGuard … (mR e.tgt)`, the same lowering as the left guards | exact |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` on the right | clocked since 2026-10-21 (branch `clocked-right`; its scope `docs/CLOCKED-RIGHT-SCOPE.md` is a planning record, last present at commit 29663d8): the right body of every bridge claim is `rightAutomatonBodyC G mv tr dt` (`ClockedTop.lean:101` to `:112`, `clockedSeg` at `BridgeReposition.lean:245`) with `dt = epsR p`, i.e. per mode `q`: `?(mv = q); tr := 0; {x' = f_q, tr' = 1 & Q_q}; ?(tr ≤ ε_R); switch`. The cap is a post-test after the flow; since the clock is monotone from `tr = 0`, it admits exactly the same runs as `& t ≤ ε_R` inside the domain (the left side already uses this form, `gwindowSeg`, `CoverExtract.lean:171`). The right clock is the fourth auxiliary coordinate `(Aux, d)`, next to `(Aux, a)` (right mode variable), `(Aux, b)` (left clock), `(Aux, c)` (stored left mode); the instance dimension is therefore the Assumption 1 lemma's dimension plus one (`bridgeDimV2`, `VerdictsV2/RunBridge.lean:74`; the lift `wellFormedR_lift` with the decided bundle `padOK`, `Emitted/Lift.lean:108`, `:292`). The response layer is `gsegC`/`RRespPC`/`guarded_rights_bridgeC` (`ClockedRight.lean:207`, `:226`, `:325`); every right flow the chain builds has an explicit duration `≤ ε_R` (the joint span `hspan`, the reposition flows of `Progress.lean`, zero-duration hops). Clock erasure, `star_bodyC_to_body` (`ClockedRight.lean:616`), shows the clocked claim implies the unclocked one; the 28 standalone instances (`InstancesV2/Modal/`, archived 2026-10-22) stated the unclocked `rightAutomatonBody` | exact (cap as post-test) |
| budgets `B = ε_L`, weights `w = ε_R/λ` (real) | `B : ℕ` segments of the common span `δ`, `B = ⌈ε_L/δ⌉` | ℕ-discretization |
| jump-then-flow (right) | flow-then-jump (`modeStepC`; `modeStep` in the kept unclocked layer): the same body up to rotation; the loop invariant therefore carries the right's current-mode guard (`op_R`) | rotation (`docs/history/ROTATION-SCOPE.md` on branch `archive/legacy-2026-10`) |
| resets | identities | matches the paper's Limitations (`docs/history/RESET-MAPS-SCOPE.md` on branch `archive/legacy-2026-10`) |
| evolve domains | each side's uniform evolve domain (every suite benchmark declares the same evolve in all modes of a side); per-mode domains (the paper's Eq. 1) are outside the Lean lift | scope |
| invariant `φInv` | `φInv ∧ envLR domL domR ∧ mvRegionR mv (regionG guard cuts)`: the envelope and the mode-consistent region are bookkeeping on both sides of the implication (`psiK` adds `u_L ∈ modes` in the keyed form) | the `str(φ)` form of the paper's Eq. 10 (`eq:strengthening`): `str(φ) → [|(L*, R*)⟩⟩ str(φ)` with `str(φ) ≡ φ ∧ op_R ∧ Q_{u_l} ∧ Q_{u_r}`; `mvRegionR` is `op_R` (with the cuts), `envLR domL domR` is `Q_{u_l} ∧ Q_{u_r}` with one domain per side (the row above) |
| Section 6.3 "Known-false inputs" (`\numrefuted` = 67 invariant variants proved to admit no certificate; relCertifier declines all) | per variant, `¬ keyedClaim IR n cX cov ⊤ 0 1 2 3 dt` / `¬ windowClaim IR n cX cov ⊤ 0 1 2 dt` (the clocked claims of the bridge instances, at the benchmark's bridge dimension `RefRec.dim + 1`) for every cover record (any pruning), at the model's cut certificate: the generic `refute_keyed_C/A/B`, `refute_window_B` refute the unclocked `keyedClaimU`/`windowClaimU` (`Refute.lean:477`, `RefuteFlow.lean:320`), and the wrappers `refute_keyed_C/A/B_clocked`, `refute_window_B_clocked` (`Refute.lean:653`, `:662`, `RefuteFlow.lean:478`, `:578`) conclude against the clocked claims by contraposition through `keyedClaim_to_unclocked` / `windowClaim_to_unclocked` (`Refute.lean:561`, `RefuteFlow.lean:331`; hypotheses `namesOK`, `cutsOK`, `d ≠ a`); instances generated by `scripts/gen_refute.py` from the untrusted finder `scripts/refute_finder.py`; Z3 groups discharged by `relcert-refute-verdicts` (188/188, unchanged by the padded coordinate); verdicts and tables in `docs/REFUTATION-RESULTS.md` | `Proofs/Encoding/Emitted/Refute.lean`, `RefuteFlow.lean`, `RefuteExit.lean`, `InstancesV2/Refute/` |

## 10. Appendices of the paper

Appendix A (Proofs) proves each numbered result on paper; the Lean names that carry the same
argument:

| appendix | paper result | Lean |
|---|---|---|
| A.1 | Lemma 1 (Time Stretching) | `sem_rightBlock_reparam_iff` (`Proofs/Encoding/Reparam.lean`), `joint_of_sols_lam` (`Proofs/Encoding/SyncSwitch.lean`) |
| A.2 | Lemma 2 (Lie Conditions) | `flow_cert_sound` (`Core/FlowCert.lean`), threaded over the components with the kept atoms by `check_sound_multi_cutX` (`Proofs/Soundness/CutLiftX.lean`) |
| A.3 | Lemma 3 (Proving Joint Segments) | the joint steps of `coverX_piece` (`Proofs/Encoding/CoverResp.lean`), with the non-connection facts `nonconn_sound` (`Checker/NonConn.lean`) and `nonconn_of_unsat` (`Proofs/Encoding/NonConnBridge.lean`) |
| A.4 | Lemma 4 (Proving Right-Only Segments) | the right-only steps of `coverX_piece` (`repoStep`), from `RepoProgress` (`CoverResp.lean`), discharged by `repoProgress_one`, `repoProgress_two`, `repoProgress_one_down` (`Proofs/Encoding/Progress.lean`) |
| A.5 | Theorem 1 (Soundness of Witness Strategies), with Lemma 6 (Node Claim) | the induction `coverX_piece` over `CoveredX`; Lemma 6's per-node claim is what `coverX_piece` states per covered configuration (every left run within the remaining budget is answered by the right); `coverX_gresp` and `Hmulti_of_coverX` lift it to the left windows |
| A.6 | Theorem 2 (Composition) | `theorem3_modeKeyed_gen` (`Proofs/Encoding/ClockedKeyed.lean`), the handoff queries read by `handoff_of_unsat` (`Proofs/Encoding/ModeHandoff.lean`) |
| A.7 | Lemma 5 (Covers Are Witness Strategies) | `CoveredX` (`Checker/CoverX.lean`) read as the tree, `decideCoveredX_sound` (the kernel's replay of the emitted cover) |
| A.8 | Theorem 3 (Soundness of Synthesis) | `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`), per benchmark `theorem3_window_of_records` (`Emitted/Window.lean`) and `theorem3_keyed_of_records` (`Emitted/Keyed.lean`) |

Appendix B (The Mechanization) corresponds to this file and `README.md`: B.1
(What Is Proved) is §6.2, B.2 (the Lean statement and Eq. 1) is §9, B.3 (where the paper lives
in Lean) is this whole file, B.4 (Trusted Base) is §7 and `RelCertifier/Trusted/README.md`, B.5
(Assumption 1) is §2.1 and `docs/WELLFORMED.md`, B.6 (Refutations) is the last row of §9 and
`docs/REFUTATION-RESULTS.md`, and B.7 (Reproduction) is `docs/CERTIFICATION-CHECK.md`.

Appendix C (Per-Benchmark Results): the per-benchmark table (Table 3) is generated from the
frozen run's matrix.

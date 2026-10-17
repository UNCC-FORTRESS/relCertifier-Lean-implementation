# Paper ↔ mechanization: the map

Read this with the paper open. One section per formal element of the paper, in the paper's
order; each says what the Lean name is, where it lives, how its hypotheses are discharged, and
which axioms it rests on. Paper references are to *Certifying Forall-Exists Invariants for
Cyber-Physical Systems via Witness Construction* (HSCC+ICCPS'27 submission), in the paper's
numbering as of 2026-10-16 (paper commit `f7dcb92`): Section 3 opens its methodology part
with a preprocessing phase, Definition 2 (Mode Invariant), and ends with, in this order,
Definition 3 (Segments), Definition 4 (Witness Strategy), Assumption 1 (Well-Formedness) and
Theorem 1 (Soundness of Witness Strategies); Section 4.1 flow certificates (Lemma 1 Time
Stretching, Definition 5 Flow Certificate, Lemma 2 Lie Conditions, Lemma 3 Joint Segments,
and "Finding mode invariants" under Discharging); Section 4.2 non-connection certificates (Definition 6); Section 4.3
reposition certificates (Definition 7, Lemma 4 Progress Functions, Lemma 5 Right-Only Segments);
Section 5 the cover (Definition 8) and Theorem 3 (Soundness of Synthesis). The repository layout and the build and check recipe are in
`README.md` and `docs/CERTIFICATION-CHECK.md`; the historical, branch-by-branch account that
this file replaces is `docs/history/PAPER-MAPPING-2026-10-10.md`.

**Numbering note.** The Lean names and docstrings keep the paper's earlier numbering and
vocabulary: in them Theorem 1 is flow certification, Theorem 2 non-connection, Theorem 3
synthesis (`theorem3Form`, `theorem3_of_coverX`, the `<b>_bridge` instances), Definition 4
the cover, and the reposition certificate is the "progress certificate" (`ProgressEmit.lean`,
`repoProgress_*`, `progressVerd_*`, `RepoProgress`); the tool keeps the name "progress" too.
Old (the paper's numbering of 2026-10-15) to new: Definition 2 / Theorem 1 (flow) →
Definition 5 / Lemma 2; Definition 3 / Theorem 2 (progress) → Definition 7 / Lemma 4, with
"progress certificate" → "reposition certificate"; Definition 4 / Theorem 3 (non-connection)
→ Definition 6, its theorem now a one-sentence consequence with no number; Definition 5
(cover) → Definition 8; Theorem 4 (synthesis) → Theorem 2; Lemma 1 (Time Stretching) → Lemma
1 (unchanged). Paper commit `c4e1c35` (2026-10-16) inserted Definition 4 (Checked Cut) in
Section 4.1, which is why the certificate definitions moved up by one from the numbering of
paper commit `e18c0cb` (earlier the same day: flow 4, non-connection 5, reposition 6, cover
7); the checked cut was already in the Lean development as the cut certificate (§2, §7).
Paper commit `f7dcb92` (later on 2026-10-16) moved that definition into Section 3 as a
preprocessing phase under the name mode invariant: Checked Cut (Definition 4, Section 4.1)
→ Mode Invariant (Definition 2, Section 3), so Segments 2 → 3 and Witness Strategy 3 → 4;
the certificate numbers (5 to 8), the lemmas and the theorems are unchanged. The paper's
`I_m` (a mode invariant of mode `m`, one per mode, `true` by default, fixed by
preprocessing) is the tool's checked cut; the Lean names keep "cut" (`checkedCut`,
`EvolStrengthening`, `CutLiftX`, the stay verdicts). The former `res(m_l)` (the residence
set) is gone from the entry states, which now read `I_{m_l} ∧ I_{m_l} ∧ g_{m_r}`, and the
former `C_l`, `C_r` are `I_{m_l}`, `I_{m_r}`. The
intermediate numbering of paper commit `4f9a85d` (earlier on 2026-10-16)
differs from the current one in the composition result and the lemmas: composition result
Lemma 1 (Composition) → Theorem 1 (Soundness of Witness Strategies); synthesis Theorem 1
(Soundness of Synthesis) → Theorem 2, then Theorem 3 once Theorem 2 (Composition) was split out of Theorem 1 (paper 85cce32); the lemmas renumber, Lemmas 2 to 6 → Lemmas 1 to 5
(Time Stretching, Lie Conditions, Joint Segments, Stage Ladder, Right-Only Segments).
New in the paper, with no Lean statement of their own: Assumption 1 moved into Section 3
(same content, with the remark that `next(q)` is adequate; the operating region `op_R` and
the admissible initial modes are now defined in Section 3), Definition 3 (Segments),
Definition 4 (Witness Strategy), Theorem 1 (Soundness of Witness Strategies), Lemma 3 (Joint
Segments) and Lemma 5 (Right-Only Segments); Definition 2 (Mode Invariant) has one, the cut
certificate (§2). Theorem 1 is the cover induction `coverX_piece`
and Lemmas 3 and 5 are steps of it (§2.2 below), as the paper's Mechanization paragraph says.
In this file "a benchmark's Theorem 3" or "a Theorem 3 instance" names that Lean statement,
which is the paper's Theorem 3; every other Definition, Lemma and Theorem number is the
paper's.

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
| **generic bridge** (the paper's route) | `InstancesV2/Bridge/<B>.lean`, `<b>_bridge` (all 50 suite benchmarks + 2 choice exhibits) | generated by `scripts/gen_bridge.py` from the emitted records; structural facts by `decide +kernel`, Assumption 1 transported from the benchmark's `WellFormedR` lemma, every Z3 fact as one `Verdicts` hypothesis discharged by `relcert-bridge-verdicts` | `docs/BRIDGE.md`; axioms: standard three + `z3_unsat_sound` |
| standalone instances (the earlier route, kept) | `InstancesV2/Modal/<B>.lean` (and `LeftAutV2.lean`, `Instances/` for the carried-over ones), listed in `BatteryV2.lean` | hand-written per benchmark: an explicit response that replays the emitted cover, each flow fact a named pack `Verd l q` discharged by `relcert --run-verdicts-v2` | `docs/REPLAY.md`, `docs/CERTIFICATION-CHECK.md` "Per-benchmark inventory"; same axioms |

The bridge is what the sentences of this map point at. The standalone route is the historical
evidence (its responses are explicit and readable) and the home of the per-benchmark findings
(`docs/GUARDED-SWITCHING.md`, `docs/SUITE-REDESIGN.md`).

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
invariants `I_m` of Definition 2; the paper's operating region `op_R`), bookkeeping that the
flow-then-jump rotation maintains at every loop boundary.
This is the `(φInv ∧ op_R) → [|(L,R)⟩⟩ (φInv ∧ op_R)` form of the paper's Theorem 3.

## 2. Section 3: mode invariants, segments, witness strategies, Assumption 1, composition

| paper | Lean | where |
|---|---|---|
| the run-time reading of a witness strategy: for each left window a chain of right segments (joint, right-only, and switches), chosen after the left run | `GResp G q P post σ` (the segments are chosen after the left run; the final successor at the end state) and the chain lemmas `RResp`/`RRespP` | `Proofs/Encoding/GuardedSwitch.lean`, `GuardedClimb.lean` |
| the operating region `op_R` and the admissible initial modes (Section 3) | the right's mode-consistent region `regionG guard cuts q` (§1) and `AdmissibleStart` (§6.1) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Anchor.lean` |
| a reposition (the right moves alone, the left frozen) | the right-only steps of `CoveredX` (`stepRepoPre`, `stepRepoPost`), the frozen left in `couple_box_dyn` | `Checker/CoverX.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| every mode switch of the witness passes the entered mode's guard | `SwitchLegal e ω := Formula.sat e.guard ω`; a right run is a sequence of legal switches (`guarded_rights_bridge`); every edge of the instance's graph carries the lowered guard of the mode it enters (`grOf_guards` in the bridge, `Gr_guards` in each standalone instance) | `Proofs/Encoding/GuardedSwitch.lean`, `Proofs/Encoding/Emitted/Data.lean` |
| **Definition 2** (Mode Invariant), the preprocessing phase: `F_m` is the flow of mode `m` (the continuous phase of Eq. 2); a formula `I_m` over the variables of `m` is a mode invariant of `m` if `g_m → I_m` and `I_m → [F_m] I_m` are valid; it then holds throughout every residence or cycle of `m`. Preprocessing fixes one `I_m` per mode (`true` by default), and every obligation about a pairing `(m_l, m_r)` assumes the strengthened invariant `I_{m_l} ∧ I_{m_l} ∧ I_{m_r}` | the tool's checked cut, the cut certificate: per kept atom the entry check O1 (implied by the mode's guard, `g_m → I_m`) and the preservation check O2 (kept by the mode's own flow, `I_m → [F_m] I_m`, by one of the three routes of §3), found by `OracleAPI.checkedCut` / `checkedCutX` (untrusted), recorded as `EvolStrengthening` / `EvolStrengtheningX` (`InstancesV2/Cuts/<b>.lean`, well formed by `cutsOK_wfX`), O2 re-sent as the stay verdicts (`Bridge.stayQueryOf`, `atomsStayC_L/R`), and lifted to "holds along every run of the mode" by `Proofs/Soundness/CutLiftX.lean`; the kept atoms (the conjuncts of `I_m`) of both modes of a pairing are part of the anchor (§2.2, §7), which is how the strengthened invariant enters every obligation | `Trusted/OracleAPI.lean`, `Checker/EvolStrengthening.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean`, `Emitted/Stay.lean` |
| **Definition 3** (Segments): `seg_joint(m_l, m_r, τ)` and `seg_r-only(m_r, S)` | no Lean definition of its own; the two segment obligations are what the joint and right-only cases of `coverX_piece` establish, §2.2 below | `Proofs/Encoding/CoverResp.lean` |
| **Definition 4** (Witness Strategy): a finite tree of right modes labelled with segments, rooted at an initial right mode `q₀` | the tree is the cover `CoveredX` walked by `coverX_piece`, §2.2 below | `Checker/CoverX.lean`, `Proofs/Encoding/CoverResp.lean` |
| **Assumption 1** (Well-Formedness), with the remark that `next(q)` is adequate | `WellFormedR`, §2.1 below; adequacy of `next(q)` is clause (ii) | `Proofs/Encoding/WellFormedR.lean` |
| **Theorem 1** (Soundness of Witness Strategies): witness strategies for every admissible initial mode of every left mode, with the handoff condition Eq. 12 at left mode changes, give the forall-exists invariance within op_R; the residence case is obligation (8) for `m_l` within `op_R` | the cover induction `coverX_piece` and its window assembly, §2.2 below; no standalone ∀∃ statement | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| **Theorem 2** (Composition): the per-mode strategies of Theorem 1 for every left mode, plus the handoff condition Eq. 12 at every declared left mode change, give the forall-exists invariance within op_R | `theorem3_modeKeyed` (Proofs/Encoding/ModeHandoff.lean:360): the mode-keyed assembly with the conditioned handoff hypothesis; the paper's Theorem 3 (synthesis) instantiates it with covers | Proofs/Encoding/ModeHandoff.lean |

### 2.1 Assumption 1 (well-formedness)

| paper | Lean | where |
|---|---|---|
| **Assumption 1**: the right model is nonblocking and complete with respect to its declared successors: from every state in a source-mode guard an evolution spanning `ε_R` exists, and every evolution of duration at most `ε_R`, the empty one included, ends in the guard of a declared successor | `WellFormedR G guard ε`: for every mode `q` and state `x` in `q`'s lowered guard and evolve domain, (i) `∃ Φ, ODESol m.sys m.dom x ε Φ`, (ii) every run of duration `t ≤ ε` ends in `guard e.tgt` for some `e ∈ G.edgesFrom q` (the self-loop included); `G` the benchmark's guarded right automaton, `ε` the file's `epsilon` | `Proofs/Encoding/WellFormedR.lean` |
| its use in Theorem 3 | the hypothesis `hwf` of `theorem3_of_coverX` (stated as `WellFormedRIn G guard reg ε`, Assumption 1 relative to a right-only region `reg` kept by the right flows; every instance takes `reg = ⊤`, the paper's form) | `Proofs/Encoding/Theorem3General.lean`, `Emitted/Region.lean` |
| verified, not assumed, per benchmark | `<ns>.<b>_wellFormedR` for all 50 right models, Z3-free (the three standard axioms), audited on every build by `InstancesV2/WellFormedBattery.lean`; transported onto the bridge's graph by `wellFormedR_transport` (same modes, every standalone edge a declared successor, decided), or stated over that graph directly (`<b>_wellFormedR_direct`, the two dRL benchmarks and `freedm_meter`) | `InstancesV2/WellFormed/`, `Instances/WellFormed/`, `Emitted/Transport.lean`; `docs/WELLFORMED.md` |
| the remark (self-loop whose guard contains the one-interval reach set, or a successor covering the rest) | the proof styles: (a) forward invariance of the guard then the self-loop, (b) exit into a successor's guard within one interval | `docs/WELLFORMED.md` §2 |
| the tool's sufficient check | `relcert --wellformed`: clause (ii) per right mode (`ok (invariant)` / `ok (exit→S)` / `UNKNOWN`), strict in `--check-quick-v2` | `Trusted/WellFormedCheck.lean` |
| the six satellites | since 2026-10-15 their right evolve domains carry the conserved momentum band (total angular momentum about each wheel axis within the wheel's capacity), and Assumption 1 holds literally; before, it was proved on that band only | `docs/WELLFORMED.md` §3, `docs/SUITE-REDESIGN.md` §19.2 |

### 2.2 Definition 3 (segments), Definition 4 (witness strategy), Theorem 1 (soundness of witness strategies), Lemma 3 and Lemma 5

The paper states two segment obligations (Definition 3), assembles them into a witness
strategy (Definition 4, a finite tree), and derives each obligation from a certificate: Lemma
3 (Joint Segments, Section 4.1) gives `seg_joint(m_l, m_r, min(ε_l, ε_r/λ))` from
`flowC(m_l, m_r, joint, λ)` through Assumption 1, Lemma 1 and the box; Lemma 5 (Right-Only
Segments, Section 4.3) gives `seg_r-only(m_r, ret(m_r))` from `flowC(m_l, m_r, right-only, ·)`
and `repoC(m_r)`, the retained successors as exits. Theorem 1 (Soundness of Witness
Strategies, Section 3) says that witness strategies for every admissible initial mode give the
per-mode obligation (8) within `op_R`; its proof splits the left execution by autonomy of the
dynamics and walks the tree. In Lean none of the three statements is a standalone theorem with
the paper's ∀∃ statement: `theorem3_of_coverX` goes from the certificate facts to the matching
directly, Theorem 1 is its cover induction and Lemmas 3 and 5 are steps of it, as the paper's
Mechanization paragraph says.

| paper | Lean | where |
|---|---|---|
| the entry states of a segment: `I_{m_l} ∧ I_{m_l} ∧ g_{m_r}`, where `I_{m_l}` is the mode invariant of `m_l` fixed by preprocessing (Definition 2): the left is inside a residence of `m_l`, where `I_{m_l}` holds | an anchor state `A l q` (`Emitted/Anchor.lean`): the row, the envelope, the guard of `q` and the kept atoms of both modes; the kept atoms of `m_l` are its checked cuts (the conjuncts of `I_{m_l}`), entered from the left guard (O1) and kept along the left flow (O2, the stay verdicts `atomsStayC_L`), which is how `I_{m_l}` holds at every entry state | `Proofs/Encoding/Emitted/Anchor.lean`, `Emitted/Stay.lean` |
| `seg_joint(m_l, m_r, τ)`: from the entry states `I_{m_l} ∧ I_{m_l} ∧ g_{m_r}`, `[|(F_{m_l}^{≤τ}, R^{m_r})⟩⟩ I_{m_l}` (the flow of `m_l` for at most `τ`, timer started at 0; one right cycle) | the joint cases of `coverX_piece` (`CoverResp.lean:232`): the partial-span case is `coverX_finish` (`CoverResp.lean:163`), the full-span branch of `step` (`CoverResp.lean:260` to `301`) inlines the same reasoning | `Proofs/Encoding/CoverResp.lean` |
| **Lemma 3** (Joint Segments): `flowC(m_l, m_r, joint, λ)` gives `seg_joint(m_l, m_r, min(ε_l, ε_r/λ))` | inside those cases: the right run of span `δ = ε_R/λ` exists by Assumption 1 clause (i); `joint_stretch` (`ReplayEngine.lean:117`) and the rescaling lemma `joint_of_sols_lam` (`SyncSwitch.lean:188`, the paper's Lemma 1) pair it with the left run as one run of the joint product program; the certificate (`hbox`) keeps the anchor along it; the end state enables a declared successor by clause (ii) | `Proofs/Encoding/CoverResp.lean`, `ReplayEngine.lean`, `SyncSwitch.lean` |
| `seg_r-only(m_r, S)` for an exit set `S ⊆ next(m_r) \ {m_r}`: with the left frozen, from the same entry states `I_{m_l} ∧ I_{m_l} ∧ g_{m_r}`, `[(R^{m_r})*] I_{m_l}` and `⟨(R^{m_r})*⟩ ⋁_{q' ∈ S} g_{q'}` | `RepoProgress` (`CoverResp.lean:100`): from a reposition start, right-only cycles of the node until a retained exit is enabled, the anchor kept throughout; consumed by `repoStep` (`CoverResp.lean:192`) inside `coverX_piece`; `S` is the retained successor set | `Proofs/Encoding/CoverResp.lean` |
| **Lemma 5** (Right-Only Segments): `flowC(m_l, m_r, right-only, ·)` and `repoC(m_r)` give `seg_r-only(m_r, ret(m_r))` | `repoProgress_one` (`Progress.lean:550`), `repoProgress_two` (`Progress.lean:582`), `repoProgress_one_down` (`Progress.lean:681`): the stage ladder, the right-only flow box (`hboxD`) and the right-only non-connection facts (`hpruneD`) prove `RepoProgress`; discharged per benchmark by `hrepoProg_of` (`Emitted/Progress.lean:195`) and handed to `theorem3_of_coverX` as the `hrepoProg` field of `CoverHyps` | `Proofs/Encoding/Progress.lean`, `Emitted/Progress.lean` |
| **Definition 4** (Witness Strategy): a finite tree rooted at an initial right mode `q₀`, nodes right modes labelled with a segment; a joint node `q` carries `seg_joint(m_l, q, τ_q)` and its children form an adequate set `S ⊆ next(q)` (every end state of a cycle of `q` from an entry state enables some `q' ∈ S`); a right-only node carries `seg_r-only(q, S)` and has exactly `S` as children; a joint node is a leaf when the `τ`'s on its branch sum to at least `ε_l` | the cover `CoveredX` (`Checker/CoverX.lean`) read as a tree: `step` is a joint node whose children are the retained successors, `stepRepoPre`/`stepRepoPost` a right-only node, `base` a leaf (the remaining budget fits one segment). The adequate set is the retained successor set `retainedSucc` in the all-successors rule and the chosen set `S` of the choice rules (`stepChosen`, `repoChosen`), whose adequacy is the coverage certificate (`hcovJ`, `hcovR`, `hcovS` in `CoverHyps`, `docs/CHOICE-SOUNDNESS.md`) | `Checker/CoverX.lean`, `Proofs/Encoding/Theorem3General.lean` |
| **Theorem 1** (Soundness of Witness Strategies): witness strategies for every admissible `q₀` of every `m_l`, plus the handoff condition Eq. 12, give the forall-exists invariance within op_R (per residence: obligation (8) for `m_l`) within `op_R`; the proof splits the left execution by autonomy and walks the tree | `coverX_piece` (`CoverResp.lean:232`): the walk of the tree, one clocked left piece answered from a node of `CoveredX` (the segment runs, the anchor is kept, a child is entered legally, the budget decreases); `coverX_gresp` (`CoverResp.lean:405`) lifts it to `GResp` over one left window; the window assembly `Hmulti_of_coverX` (`Theorem3General.lean:128`) splits the left execution into windows and quantifies over the admissible starts | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean` |
| an older single-segment route (not used by `theorem3_of_coverX`) | `segment_faModal` (`Core/Reify.lean:100`) and `segment_relational` (`EncodingBridge.lean:53`): ∀∃ segment theorems with a carried duration-existence side condition | `Core/Reify.lean`, `Proofs/Encoding/EncodingBridge.lean` |

## 3. Section 4.1: flow certificates (Lemma 1, Definition 5, Lemma 2, Lemma 3) and "Finding mode invariants"

| paper | Lean | where |
|---|---|---|
| the joint product program `α_joint^λ` (Eq. 13): `ẋ_L = f_L`, `ẋ_R = λ f_R`, under both evolve domains | `Program.ode (jointSys fL fR (Term.const λ)) (domL ∧ domR)` | `Core/FlowCert.lean` |
| the right-only product program `α_right-only` (Eq. 14): left frozen | `rightBlock fR` with the left coordinates unmoved (`mergeLR`), the dynamic reposition program | `Proofs/Encoding/ReplayDyn.lean`, `RepoPrefixR.lean` |
| **Lemma 1** (Time Stretching): `φ` solves `ẋ = f` on `[0, λτ]` iff `s ↦ φ(λs)` solves `ẋ = λf` on `[0, τ]` | `sem_rightBlock_reparam`, `sem_rightBlock_reparam_iff`; the right projection of a joint run time-rescaled, `odeSol_right_of_joint`; the joint rescaling used by the cover induction, `joint_of_sols_lam` | `Proofs/Encoding/Reparam.lean`, `Emitted/Region.lean`, `SyncSwitch.lean` |
| Eqs. 15 to 17: the Lie-derivative conditions over the domain and the mode invariants `I_{m_l} ∧ I_{m_r}` (the tool's checked cuts; the tool's sufficient condition) | the three query routes of one component: whole-domain `dom ∧ ġ > 0` (route A), boundary `dom ∧ g = 0 ∧ ġ ≥ 0` (route B), superlevel `dom ∧ g ≥ 0 ∧ ġ > 0` (route C), each `unsat`; the **pack** of a pairing `(l, q)` at its stretch: one `unsat` per component by any of the three routes, over the segment domain narrowed by the kept atoms (the checked cuts), in the strata order the tool recorded (`modalVerdXQueries`); the reposition pack `modalVerdDynXQueries` for the right-only kind | `Core/FlowCert.lean` (`flowQuery`, `flowQueryStrict`, `lieDeriv`, `tderiv_correct`), `Proofs/Flow/DISuperlevel.lean`, `VerdictsV2/ModalX.lean`, `ModalDynX.lean` |
| "Finding mode invariants" (under Discharging): the tool's preprocessing, its checked cuts, which find the `I_m` of Definition 2 | the cut certificate, the Definition 2 row of §2 (`OracleAPI.checkedCut` / `checkedCutX`, `EvolStrengthening(X)`, the stay verdicts, `CutLiftX`) | `Trusted/OracleAPI.lean`, `Checker/EvolStrengtheningX.lean`, `Proofs/Soundness/CutLiftX.lean` |
| **Definition 5** (Flow Certificate): `flowC(m_l, m_r, kind, λ)` consists of (1) a mode invariant `I_{m_l}` of `m_l`, (2) a mode invariant `I_{m_r}` of `m_r`, and (3) a proof that `I_{m_l} ∧ I_{m_l} ∧ I_{m_r} ∧ g_{m_r} → [α_kind^λ] I_{m_l}` is valid (preservation from the entry states within the mode invariants) | items (1) and (2): the cut certificates of the two modes (Definition 2, §2); item (3): the box as the general theorem consumes it, the `hbox` field of `CoverHyps` (joint kind: the anchor kept along every run of the stretched joint flow from an anchor state, the anchor carrying both modes' kept atoms) and the hypothesis `hboxD` of the `repoProgress_*` lemmas (right-only kind: the anchor kept along the frozen-left flow); per segment `couple_box_cutX` (joint) and `couple_box_dyn` (right-only) | `Proofs/Encoding/Theorem3General.lean`, `Progress.lean`, `SyncSwitch.lean`, `ReplayDyn.lean` |
| **Lemma 2** (Lie Conditions): the conditions over the domain strengthened by `I_{m_l} ∧ I_{m_r}` prove item (3) of Definition 5 | `flow_cert_sound` (one component: an `unsat` route query gives `BoxLe` along the stretched joint flow, through dL-lean's `DI_nonstrict_domain`); threaded over the components with the kept atoms by `check_sound_multi_cutX` | `Core/FlowCert.lean`, `Proofs/Soundness/CutLiftX.lean` |
| **Lemma 3** (Joint Segments): `flowC(m_l, m_r, joint, λ)` gives `seg_joint(m_l, m_r, min(ε_l, ε_r/λ))` | a step of `coverX_piece`, §2.2 | `Proofs/Encoding/CoverResp.lean` |
| the tool's query, the runner's query and the theorem's hypothesis are the same formula | the runner rebuilds each query from the committed records with the tool's own lowering and printer; the verdict pins (`VerdictsV2/PinsV2.lean`, `LamPinV2.lean`) tie each pack and its stretch to the emitted cover; in the bridge, `Verdicts` is by definition the runner's group list (`Emitted.verdicts_of_groups`) | `VerdictsV2/`, `Proofs/Encoding/Emitted/Run.lean` |

Existence of the right flow for the needed duration is not part of Definition 5 or Lemma 2 in
the paper; Lemma 3 draws it from Assumption 1, and so does Lean (clause (i), §2.1), used by
the general theorem, and in the standalone instances an explicit solution or a viability
argument (`Proofs/Flow/`).

## 4. Section 4.2: non-connection certificates (Definition 6)

| paper | Lean | where |
|---|---|---|
| the programs `β_joint` (one cycle of the right mode; the stretch is dropped by Lemma 1) and `β_right-only` | the right flow of the stretched joint program and the frozen-left flow, as under Definition 5 | `Core/FlowCert.lean`, `Proofs/Encoding/ReplayDyn.lean` |
| **Definition 6** (Non-Connection Certificate): a non-connection certificate for `m_R → m_R'` proves `C^σ → [β_kind^λ] ¬N` (no entry state of the target is reached) | the two checks as the tool sends them, `NonConn.queries` (source: no entry state of `m_R` satisfies the threshold guard; barrier: on the threshold the flow moves the variable away), defined once for the certifier, the runner and the kernel | `Trusted/NonConnQuery.lean` |
| the consequence sentence after Definition 6 (the old Theorem 3; no numbered statement): the declared change is never taken under `(σ, kind)` | `nonconn_sound` (dL-lean `DI_strict` on the safe-side term); `nonconn_of_unsat`: the runner's two `unsat` answers are its hypotheses | `Checker/NonConn.lean`, `Proofs/Encoding/NonConnBridge.lean` |
| the remark that removing a pruned successor keeps a set adequate; where a pruned edge leaves the cover | `SearchGraph.retainedSucc` (`Checker/Cover.lean:100`) drops it; the cover record carries the `pruned` list the kernel replays; in `coverX_piece` the end state of a joint segment enables a declared successor (Assumption 1 clause (ii)) whose guard is excluded for every pruned exit (`guard_pos_of_barrier`), so the retained set is still adequate | `Checker/Cover.lean`, `Checker/CoverX.lean`, `Proofs/Encoding/Emitted/Barrier.lean` |
| where it enters Theorem 3 | the bridge keeps the barrier term of every pruned exit of the current right mode in the anchor: `≤ 0` on entry (source check), kept along joint and frozen flows (barrier check), `> 0` under the target's guard, so the target's guard never holds at a segment end (`nonconn_entry`, `nonconn_keep`, `guard_pos_of_barrier`; the general theorem's `hprune` field of `CoverHyps`, and `hpruneD` of the `repoProgress_*` lemmas for the right-only kind) | `Proofs/Encoding/Emitted/Barrier.lean` |
| suite | 44 pruned edges, both queries of each discharged (`--run-verdicts-v2`, and as groups of `relcert-bridge-verdicts`); the per-edge instance `match_multi_rate_nonconn` for `DRIVE → STALL` (its docstring says "Theorem 2", the Lean docstring numbering) | `VerdictsV2/NonConnPinV2.lean`, `Instances/MatchMultiRatePruned.lean` |

## 5. Section 4.3: reposition certificates (Definition 7, Lemma 4, Lemma 5)

The paper calls them reposition certificates; the tool and Lean call them progress
certificates (`Trusted/ProgressEmit.lean`, `Proofs/Encoding/Progress.lean`,
`VerdictsV2/ProgressPin.lean`, `relcert-progress-verdicts`).

| paper | Lean | where |
|---|---|---|
| the region of the stage-ladder queries, `R_q ≡ D_{m_r} ∧ I_{m_l} ∧ I_{m_r} ∧ I_{m_l}` (the right evolve domain, the mode invariants of both modes (the tool's checked cuts), the invariant; defined under "Discharging the obligation"); retained successors `ret(q)` = declared, non-self, not pruned by a non-connection certificate | the node's region (the anchor `A q`, its kept atoms, the right domain); `retainedSucc` | `Checker/Cover.lean`, `Emitted/Anchor.lean` |
| **Definition 7** (Reposition Certificate): with the mode invariants `I_{m_l}` of `m_l` and `I_{m_r}` of `m_r` (Definition 2), `repoC(m_r)` is a proof that `I_{m_l} ∧ I_{m_l} ∧ I_{m_r} ∧ g_{m_r} → ⟨β_right-only⟩ ⋁_{q' ∈ ret(q)} g_{q'}` is valid | the conclusion of the `repoProgress_*` lemmas, `RepoProgress` (`CoverResp.lean:100`): from a reposition start, cycles of the node until a retained exit is enabled, the anchor kept | `Proofs/Encoding/CoverResp.lean` |
| the stage ladder (Eqs. 18 to 20, rate / keep / land), the tool's sufficient condition | per reposition node: staged rate bounds (`rateQuery`), kept thresholds (`keepQuery`) and the landing (`landQueries`: on the crossing line and at an already-crossed start some exit's guard holds); emitted by default (`RELCERT_NO_PROGRESS=1` disables it) | `Trusted/ProgressEmit.lean` |
| **Lemma 4** (Progress Functions): the ladder implies `repoC` with the cycle bound | `repoProgress_one` (`Progress.lean:550`), `repoProgress_one_down` (`Progress.lean:681`, a single downward stage) and `repoProgress_two` (`Progress.lean:582`), standard axioms; `progressVerd_one/one_down/two` (`VerdictsV2/ProgressPin.lean`) read the runner's `unsat` answers as its facts | `Proofs/Encoding/Progress.lean`, `VerdictsV2/ProgressPin.lean` |
| **Lemma 5** (Right-Only Segments): `flowC(m_l, m_r, right-only, ·)` and `repoC(m_r)` give `seg_r-only(m_r, ret(m_r))`, the retained successors as exits | a step of `coverX_piece`, §2.2: `hrepoProg_of` (`Emitted/Progress.lean:195`) folds the ladder facts, the right-only flow box `hboxD` and the right-only non-connection facts `hpruneD` into `RepoProgress`, the `hrepoProg` field of `CoverHyps`, consumed by `repoStep` | `Proofs/Encoding/Emitted/Progress.lean`, `CoverResp.lean` |
| suite | 261 certificates, all discharged (`relcert-progress-verdicts`) | `docs/THEOREM3-GENERAL.md` §3 |

Why the premise is needed: the proof sketch of the synthesis theorem says Assumption 1
"continues every segment along a retained edge". For a right-only segment that is not enough:
Assumption 1 may enable only the self-loop, the right-only case of Definition 8 needs a non-self
exit, and nothing in Definition 5 says one is reached. The general theorem therefore takes
`hrepoProg : RepoProgress …`, which the reposition certificate discharges.

## 6. Section 5: the cover and Theorem 3

### 6.1 Definition 8 (all-successors cover)

| paper | Lean | where |
|---|---|---|
| configuration `(m_R, B, σ)` with budget `B` and source setting `σ ∈ {pre-joint, post-joint}` | `Config = ⟨q, B, SrcSetting⟩`, `B : ℕ` segments (the budget `⌈ε_L/δ⌉`, `δ = ε_R/λ` the common span) | `Checker/Cover.lean` |
| weights: the certified segment durations `τ_{m_r} = min(ε_l, ε_r/λ)`; node kinds from Lemma 3 (joint) and Lemma 5 (right-only) | the segment span `δ` of the pairing's stretch, `B` segments per window; the cover flags `jointOK` and `dynPre`/`dynPost` | `Checker/CoverEmit.lean`, `Emitted/Data.lean` |
| a cover from `(q₀, ε_l, pre-joint)` read as a witness strategy (Definition 4): joint children = the retained successors, adequate by Assumption 1 and Section 4.2; right-only children = the exits of Lemma 5 | no separate reading: `coverX_piece` walks `CoveredX` directly (§2.2); the retained successor set `SearchGraph.retainedSucc` is the adequate set of a joint node, the exits of a right-only node are the retained exits of `RepoProgress`; for the choice rules the chosen set `S` is adequate by its coverage certificate (`hcovJ`, `hcovR`, `hcovS`) | `Proofs/Encoding/CoverResp.lean`, `Checker/Cover.lean` |
| case 1: a prefix of the certified joint segment finishes the residence | `CoveredX.base` | `Checker/CoverX.lean` |
| case 2, joint kind: every retained successor covered at `B − w` with `σ' = post-joint` | `CoveredX.step` | |
| case 2, right-only kind: every retained exit covered, `σ` unchanged | `CoveredX.stepRepoPre`, `stepRepoPost` | |
| "only configurations reached by finitely many applications" | `CoveredX` is inductive; the checker `decideCoveredX` is fuel-bounded (`fuelOf`); `decideCoveredX_sound` says an accepted configuration is covered | `Checker/CoverX.lean` |
| the search graph: certified kinds, weights, retained edges | the emitted cover record `CoverEmitE` (flags per node: `jointOK`, `dynPre`/`dynPost`; stretches; pruned edges; admissible starts; strata orders) replayed in the kernel: `CoverReplay.lean` (standalone, `decide`) and `coversOK` (bridge, `decide +kernel`) | `Checker/CoverEmit.lean`, `InstancesV2/CoverReplay.lean`, `Emitted/Keyed.lean` |
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

> `φInv ∧ op_R → [|(L,R)⟩⟩ (φInv ∧ op_R)` if (1) `R` satisfies Assumption 1; (2) for every
> `m_L` every admissible `q₀` admits an all-successors cover from `(q₀, ε_L, pre-joint)` at
> `φ_inv(m_L)`; (3) every declared left mode change satisfies the handoff condition
> (Eq. handoff).

Mechanized as `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`, standard axioms
only; the Z3 axiom enters only through the instances' verdict hypotheses). The paper proves
Theorem 3 by Theorem 2 (Composition), which applies Theorem 1 (Soundness of Witness Strategies) per residence and the handoff condition at left mode changes. The
paper's Mechanization paragraph: the Lean theorem goes from the certificate facts to the
matching directly; Theorem 1 is its cover induction and Lemmas 3 and 5 are steps of it, none a
standalone statement (§2.2).

| paper condition | Lean hypothesis | discharged in an instance by |
|---|---|---|
| (1) Assumption 1 | `hwf : WellFormedRIn Gr guard reg epsR` | the benchmark's `WellFormedR` lemma (§2.1) |
| (2) the covers, per `m_L` and admissible `q₀` | `hcov : ∀ l q, AdmissibleStart … → CoveredX Gr (ch l) ⟨q, B l, preJ⟩`, with `hdt : dt ≤ B l · δ l` (the window fits the budget) | covered starts by `decideCoveredX` on the emitted record (`coversOK`), the other starts inadmissible by their `unsat` (`adm_sound`) |
| (2), what each cover step consumes (Definitions 5, 6 and 7, and the segment-level facts) | `H : ∀ l, CoverHyps …` (`Theorem3General.lean:40` to `71`), whose fields are: the flow certificate of every certified joint pairing at its stretch (`hbox`); the non-connection certificates of the pruned edges (`hprune`); the entry condition (`hhand`: the anchor of `q` and the guard of `q'` give the anchor of `q'`); the reposition-progress premise (`hrepoProg : RepoProgress …`, §5); the coverage certificates of chosen sets (`hcovJ/R/S` with their regions `hRJ/RR/RS`, vacuous for the suite); and the side conditions `hlam`, `hspan`, `hAfv`, `hAdom`. The right-only flow box (`hboxD`) and the right-only non-connection fact (`hpruneD`) are not fields: they are hypotheses of the `repoProgress_*` lemmas (`Progress.lean:170`, `:173`) and are folded into `RepoProgress` when it is discharged | the bridge's `coverHyps_of` from the `Verdicts` structure (`Emitted/Keyed.lean`); `hrepoProg` by `hrepoProg_of` (`Emitted/Progress.lean:195`) |
| the loop invariant's right bookkeeping (`op_R`) | the anchor `A l q` (`hAstart`, `hApost`): the row, the kept atoms of both modes, the barrier terms of `q`'s pruned exits, the envelope; its region part `regionG guard cuts q` | `Emitted/Anchor.lean` (`AG`, `AG_start`, `AG_post`) |
| (3) the handoff condition (Eq. handoff): `φ_inv(m_L) ∧ dom_{m_L} ∧ guard_{m_L'} ∧ dom_{m_R} → φ_inv(m_L'), for a change from m_L to a successor m_L' ∈ next(m_L)` | for mode-dependent rows, the hypothesis `hhand` of `theorem3_modeKeyed`; the runner's query `Handoff.queryOf` is exactly this implication with the declared domains conjoined (`handoff_of_unsat`, `handoff_sound`) | `Proofs/Encoding/ModeHandoff.lean`, `Trusted/Handoff.lean`, `Emitted/Barrier.lean` |
| the conclusion | `rvalid (theorem3Form (bigChoice (leftProgsOf …)) (rightAutomatonBody Gr mv) ((canonInvM g gs ∧ envLR domL domR) ∧ mvRegionR mv (regionG guard cuts) …))`: one declared row (`theorem3_window_of_records`, `windowClaim`); for per-mode rows the composition through `theorem3_modeKeyed` over `leftAutomatonBody` with `psiK` (`theorem3_keyed_of_records`, `keyedClaim`) | `Emitted/Window.lean`, `Emitted/Keyed.lean` |
| the proof: Theorem 1 (Soundness of Witness Strategies) on the cover read as a witness strategy, plus the handoff condition | `coverX_piece` (`CoverResp.lean:232`): per case of `CoveredX`, the segment runs (Assumption 1 clause (i)), the anchor is preserved (Definition 5), the end state enables a declared successor (clause (ii)) that is not pruned (Definition 6), the switch is legal and the entered anchor holds (`hhand`); the budget decreases; the joint cases are the paper's Lemma 3 and the right-only cases (`repoStep`, from `RepoProgress`) its Lemma 5; `coverX_gresp` and `Hmulti_of_coverX` assemble the windows (Theorem 1); the handoff condition enters through `theorem3_modeKeyed` | `Proofs/Encoding/CoverResp.lean`, `Theorem3General.lean`; `docs/THEOREM3-GENERAL.md` §2 |

The mode-dependent case (the paper's twelve benchmarks): `theorem3_modeKeyed` composes the
per-mode window responses with the handoff condition and the side conditions on `u_L`
(freshness, footprints); the bridge supplies the per-mode responses through `hstepMode_GR` and
`HMode_regionG`. Mode-independent rows take the window form directly (`rowsSame` decided).

## 7. Section 6: implementation and evaluation

| paper | Lean / tool | where |
|---|---|---|
| "a Lean 4 executable; its search is untrusted and only proposes; every cover it proposes is replayed by a kernel-verified checker; a small trusted layer parses, lowers, prints and talks to Z3" | `relcert` (`Main.lean`); the trusted surface, file by file, in `RelCertifier/Trusted/README.md`: parser (`Parse.lean`, `KeyAudit.lean`), lowering (`Run.lean`, `JointVars.lean`, `InvComponents.lean`, the query builders `Handoff.lean`, `NonConnQuery.lean`, `BridgeQueries.lean`, `ProgressEmit.lean`, `ChoiceEmit.lean`), printer (`Smt.lean`), Z3 (`Z3.lean`, `Oracle.lean` with the axiom), the untrusted certifier `OracleAPI.lean` | `RelCertifier/Trusted/` |
| flow certificates and the stretch: three routes per component; one stretch per left mode, else a stretch per pairing with the common span `ε_R/λ̂` | the routes as in §3; the stretch per pairing `lam l q`, the common span `δ l = ε_R / lamQ l`, the budget `⌈ε_L/δ⌉` (`Emitted/Data.lean`); the stretch of every pack kernel-checked against the emitted cover (`LamPinV2.lean`) | `Trusted/OracleAPI.lean`, `VerdictsV2/LamPinV2.lean` |
| non-connection pruning (threshold guards, two checks) | §4 | |
| reposition certificates (the tool's progress certificates) | §5 | |
| handoff check (negation of Eq. handoff `unsat`, issued and counted for every declared left transition) | `Handoff.queryOf`; 187 transitions over the suite, all `unsat` (`docs/HANDOFF.md`) | `Trusted/Handoff.lean` |
| the cover and its budget (depth-first recursion, budget-neutral cycles rejected) | §6.1; `decideCoveredX` with fuel is the kernel's replay of the same recursion | `Checker/CoverX.lean` |
| checked cuts (the paper's mode invariants, Definition 2 in Section 3, and "Finding mode invariants" under Discharging in Section 4.1; §2: the atoms implied by a mode's guard and preserved by its own flow narrow the segment domain; the `I_{m_l} ∧ I_{m_r}` of Eqs. 15 to 17 and of `R_q`) | O1 (entry) and O2 (invariance) per kept atom; the extended certificate `EvolStrengtheningX` kernel-checked well formed (`InstancesV2/Cuts/<b>.lean`, `cutsOK_wfX`); O2 in the bridge as the stay verdicts by the certificate's route (`Bridge.stayQueryOf`, `atomsStayC_L/R`); the lift `Proofs/Soundness/CutLiftX.lean` | `Checker/EvolStrengtheningX.lean`, `Emitted/Stay.lean` |
| "Mechanization" paragraph: a kernel-checked theorem per benchmark over the guard-gated programs; Z3 hypotheses tied to the exact queries; trust base = parser, lowering, printer, Z3 `unsat`, kernel; twelve mode-dependent benchmarks composed with handoffs; Assumption 1 proved per benchmark; Theorem 1 (Soundness of Witness Strategies) as the cover induction, Lemmas 3 and 5 as steps of it, none a standalone statement | §0 (both routes), §6.2, §2.1, §2.2. Counts to quote: 50 benchmarks (46 designed, 4 from the literature); bridge verdicts 4457 groups, 4321 over the suite (`relcert-bridge-verdicts`, the number the paragraph quotes); standalone packs 234 joint + 41 reposition over 1410 verdict hypotheses for the 46 original benchmarks (`--run-verdicts-v2`); handoff 401; non-connection 88 over 44 pruned edges; progress 261; Assumption 1: 50 of 50 | `STATUS.md`, `docs/VERDICTS.md` |
| the benchmark table (tab:benchmarks) and the mechanism matrix | `scripts/suite_v2_matrix.py`, `scripts/paper_numbers.sh` (the frozen numbers the paper quotes) | `docs/SUITE-REDESIGN.md` |

**Paper text, checked against paper commit `4f9a85d` (2026-10-16).** The items listed here
on 2026-10-15 (paper commit `da28aa9`) are resolved: the Mechanization paragraph now takes the
certificates, the handoff conditions and Assumption 1 as hypotheses of one Lean theorem over
the guard-gated programs, quotes the 4321 `unsat` answers over the suite re-sent by a runner,
says Assumption 1 is proved per benchmark, and names the trust base (parser and lowering,
query printer, Z3 `unsat`, kernel); the 1410 count, the "momentum-feasible region" and the
"nominal response" sentences are gone, and the Scope paragraph says the satellites declare the
momentum bound. Nothing in the paper beyond Section 4.3 describes the reposition certificate
(§5), which is fine: the paragraph's "certificates" covers it.

## 8. Where the numbers come from

| number | source |
|---|---|
| 50 benchmarks, all CERTIFIED with `RELCERT_IMPLIED_CUT=1` (4 need the existential mode choice, the default) | `scripts/paper_numbers.sh` (frozen), `benchmarks/suite_v2/` |
| 52 bridge instances, 4457 verdict groups (4321 over the 50 suite benchmarks, 136 over the 2 exhibits) | `InstancesV2/Bridge.lean`, `relcert-bridge-verdicts`, `expectedBridgeGroupsV2` |
| 46 standalone instances (the original benchmarks; `vehicle_hypercert`'s in `InstancesV2/Choice/`), 234 joint + 41 reposition packs, 1410 hypotheses | `InstancesV2/BatteryV2.lean`, `relcert --run-verdicts-v2`, `docs/VERDICTS.md` |
| 44 pruned edges, 88 non-connection queries; 401 handoff queries; 261 progress (reposition certificate) queries | the same runner; `relcert-progress-verdicts` |
| Assumption 1: 50 of 50, Z3-free | `InstancesV2/WellFormedBattery.lean` |
| axioms of every instance: `propext`, `Classical.choice`, `Quot.sound`, `z3_unsat_sound` | `lake build … 2>&1 | grep -A3 "depends on axioms"`; `docs/CERTIFICATION-CHECK.md` check 2 |

## 9. Modelling choices to state in the paper

| paper `cpsProg` | mechanized | direction |
|---|---|---|
| left has guards, `u_L`, clock | `leftAutomatonBody` with the lowered left guards, the declared `next` lists and `u_L`, windows clock-capped (mode-independent rows through `bigChoice` of the windows, carried by `theorem3_leftAut_of_choice`) | exact (jump then flow, as the paper writes it) |
| `?guard_m(x)` on right transitions | every edge carries `hostGuard … (mR e.tgt)`, the same lowering as the left guards | exact |
| `t := 0; {…, t' = 1 & t ≤ ε_R}` on the right | unclocked in `rightAutomatonBody`; durations are the ∃-side's choice, bounded by the budget | permissive |
| budgets `B = ε_L`, weights `w = ε_R/λ` (real) | `B : ℕ` segments of the common span `δ`, `B = ⌈ε_L/δ⌉` | ℕ-discretization |
| jump-then-flow (right) | flow-then-jump (`modeStep`): the same body up to rotation; the loop invariant therefore carries the right's current-mode guard (`op_R`) | rotation (`docs/history/ROTATION-SCOPE.md`) |
| resets | identities | matches the paper's Limitations (`docs/history/RESET-MAPS-SCOPE.md`) |
| evolve domains | each side's uniform evolve domain (every suite benchmark declares the same evolve in all modes of a side); per-mode domains (the paper's Eq. 2) are outside the Lean lift | scope |
| invariant `φInv` | `φInv ∧ envLR ∧ mvRegionR mv (regionG guard cuts)`: the envelope and the mode-consistent region are bookkeeping on both sides of the implication | the `(φInv ∧ op_R)` form of the paper's Theorem 3 |

# Existential mode choice: soundness argument

Status: argument first, code second. The region builders in `Trusted/OracleAPI.lean`
(`ChoiceCtx.jointEnd`, `repoEnd`, `startReg`) must match §3 exactly.

## 1. Setting

Fix a left mode `m_l` and its residence (one left control cycle, duration `τ_l ≤ ε_l`).
A configuration is `(q, B, σ, h)`: current right mode, remaining budget, source setting
(`pre-j` before the first joint segment of the residence, `post-j` after), and a hop flag
(`canHop` / `noHop`).

Semantics used (Lean: `GResp`, `Proofs/Encoding/GuardedSwitch.lean`): the right's response to
one left residence is a finite chain of right segments, each a flow of one right mode followed
by a declared switch whose target guard holds at the switch state (`SwitchLegal`), chosen
after the left run is fixed. A zero-duration segment (a hop, `gresp_hop`) is allowed when the
state lies in the source mode's evolution domain and the entered guard holds.

## 2. Facts available at the two kinds of state

**Configuration start** (the residence start, or right after a switch or hop into `q`):

* (S1) right state in `guard(q)`: at the residence start by `op_R`; after a switch or hop by
  `SwitchLegal`;
* (S2) right checked cuts of `q`: implied by `guard(q)` (entry check of the cut certificate);
* (S3) both evolution domains: part of the loop invariant (Lean: `envLR`), and every run stays
  in its domain;
* (S4) left evolution domain and left checked cuts of `m_l` (cuts hold throughout a left
  residence);
* (S5) the invariant row of `m_l`: at the residence start by the premise; afterwards by
  Theorem 1 (flow certificates hold throughout each segment, complete or partial);
* (S6) if `σ = pre-j`: the left guard of `m_l` (the left has not moved yet).

**Segment end** (after a joint segment of any duration up to its span, or a right-only
segment of any duration):

* (E1) both evolution domains (the run stays in them);
* (E2) right checked cuts of `q` (preserved by `q`'s flow, true at entry by S2);
* (E3) left domain and left checked cuts of `m_l` (S4; a right-only segment freezes the left);
* (E4) the invariant row of `m_l` (Theorem 1);
* (E5) right-only segment with `σ = pre-j` only: the left guard (left frozen, S6). A joint
  segment moves the left, so (E5) is **not** available after it.
* `guard(q)` is **not** available at a segment end: the flow may leave it.

## 3. The regions (what the code must build)

| Region | Conjuncts | Used by |
|---|---|---|
| `JointEnd(q)` | E1 ∧ E2 ∧ E3 ∧ E4 | chosen successors after a joint segment |
| `RepoEnd(q, σ)` | E1 ∧ E2 ∧ E3 ∧ E4, plus E5 if `σ = pre-j` | chosen successors after a right-only segment |
| `StartRegion(q, σ)` | S1 ∧ S2 ∧ S3 ∧ S4 ∧ S5, plus S6 if `σ = pre-j` | hop out of `q` |

Each is an over-approximation of the states at which the corresponding switch can occur. A
**coverage certificate** `Cover(R, S)` is the Z3 verdict `R ∧ ⋀_{q'∈S} ¬guard(q')` unsat, hence
`∀ μ ∈ R. ∃ q' ∈ S. guard(q')(μ)`.

Prototype check (`relcert-choice.patch`, `mkCtx`): `jointEnd = leftFacts false ∧ rightFacts`,
`repoEnd = leftFacts pre ∧ rightFacts`, `startReg = repoEnd ∧ guard(q)`, with
`leftFacts = evolveL ∧ cutL ∧ invariant rows [∧ guardL if pre]` and
`rightFacts = evolveR(q) ∧ cutR(q)`. This matches the table. The right domain in
`StartRegion` is `evolveR(q)` of the source mode, which is what `gresp_hop` needs.

## 4. Extended Definition 4

`(q, B, σ, h)` is covered if one of:

1. **base**: joint certified at `q`, `B ≤ w(q, joint)`;
2. **step, all successors** (old rule): kind `κ` certified at `q`, `w(q, κ) < B` for joint
   (`0 < B` for right-only), every retained successor `q'` of `κ` leads to a covered
   `(q', B − w, σ', canHop)`;
3. **step, chosen successors**: as 2, but for a nonempty `S` ⊆ retained successors with
   `Cover(JointEnd(q), S)` (joint) or `Cover(RepoEnd(q, σ), S)` (right-only), every `q' ∈ S`
   covered;
4. **hop**: `h = canHop`, nonempty `S` ⊆ declared non-self successors of `q` with
   `Cover(StartRegion(q, σ), S)`, every `q' ∈ S` leads to a covered `(q', B, σ, noHop)`.

`σ' = post-j` after a joint segment, `σ` otherwise. Covered is the least set closed under 1 to 4.

**Finiteness.** Joint steps lower `B` by at least the smallest positive weight; a hop sets
`noHop`, which only a segment (cases 1 to 3) resets; budget-neutral cycles of right-only steps
are excluded by the least reading (the tool rejects a revisit of an in-progress configuration).

## 5. Soundness (existence of the response)

By induction on the finite cover, from a configuration start satisfying S1 to S6:

* **case 1**: run the joint segment for the rest of the residence; the invariant holds
  throughout (Theorem 1); no switch inside the residence.
* **case 2**: run the segment to its end; Assumption 1 (completeness) gives an enabled declared
  successor; non-connection certificates exclude the pruned ones (Theorem 2); every retained
  one is covered. Switch (`SwitchLegal`), arriving at a configuration start satisfying S1 to S6.
* **case 3**: run the segment to its end; the end state satisfies `JointEnd(q)` (resp.
  `RepoEnd(q, σ)`) by E1 to E5; the coverage certificate gives `q' ∈ S` with `guard(q')`
  true there; switch along that declared edge; `q'` is covered. **Assumption 1's completeness
  is not used.**
* **case 4**: the state satisfies `StartRegion(q, σ)` by S1 to S6; the certificate gives
  `q' ∈ S` with `guard(q')`; hop (`gresp_hop`: domain by S3, guard by the certificate); the
  state is unchanged, so S2 to S6 still hold for the new configuration and S1 holds for `q'`.

Segment durations: a joint segment of a step case runs its span `ε_r/λ` of left time, which is
a full right cycle at the common stretch and a partial one (`λ_q δ ≤ ε_r`) under the
per-pairing fallback; the regions assume neither, so both are covered. A segment cut short by
the end of the residence occurs only in case 1.

At the end of the residence the right takes the boundary switch of Theorem 3 (any enabled
successor, by Assumption 1); the next residence's obligation quantifies over every admissible
start mode, so choice never has to look across a left-cycle boundary.

## 6. Assumptions, stated

* **Hop (H).** A right cycle may have duration zero: at a configuration start the right may
  switch without flowing. Lean's `gresp_hop` requires the state to be in the source mode's
  evolution domain, which S3 gives. To check per model: the suite discipline gives every right
  mode the same evolution domain (`uniformEvolveR`), so S3 is the shared envelope; for the
  three exhibits, confirm the same.
* **Assumption 1.** Nonblocking is still needed (a segment can run to its end). Completeness is
  needed only for case 2 and the residence-end switch.
* Choice is within a residence plus the hop; no choice across left-cycle boundaries, no
  existential initial state.

## 7. What must be true of the code

1. Region builders as in §3 (prototype matches; keep it, add a comment pointing here).
2. The old rule runs over the whole stretch loop (and the per-pairing fallback) before any
   choice search, so the 46 emitted covers are unchanged.
3. Hop targets are declared, non-self successors; requiring them non-pruned is conservative
   and harmless (a hop has no flow).

## 8. Lean status (the three exhibits)

`RelCertifier/InstancesV2/Choice/Modal/` proves modal Theorem 3 for `vehicle_hypercert`,
`vehicle_accel_copy` and `watertank_choice`, standalone (not replayed from the tool's choice
cover). Each response is case 4 then case 1: a hop (`gresp_hop`) into one chosen mode, then
that mode's certified joint segment for the whole window. The hop's domain premise is S3
(`envLR`; every exhibit has a uniform right evolution domain), its guard premise is the left
guard plus the invariant at the start (the left run frames the right).

Existence of the right segment: `WellFormedFlowB` (existence from every domain state) is false
for constant fields at the domain edge they point to. `vehicle_hypercert` uses the mirror
argument (`hExistSegB_constMirror`: the right copies the left run). `vehicle_accel_copy` needs
the right guard at the start and one control period (`dt ≤ 1`), facts that hold at the start
but are not invariant, so it couples through `couple_cutX_at`, which takes the existence
premise at the start state only (the same proof as `couple_cutX`).

Residuals: 14 verdict packs, pinned to the instances' hypotheses (`Choice/Verdicts.lean`);
`relcert-choice-verdicts` reports all 28 components `unsat`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`, `z3_unsat_sound`.

# Roadmap: end-to-end guarantee on all benchmarks (task H closure)

Held to the FROZEN hypothesis contract: trust base (parser, lowering, printer, Z3, kernel)
+ successor-completeness. Nothing else assumed. Each item has an acceptance gate; an item
is done when its gate is kernel-green, committed, and pushed. Tackle strictly in order.

## R1 — witness extraction: `emit_from_covered`
Replace the assumed `EmitSegs`/`EmitWindows` devices: by induction on the `Covered`
derivation (from `decideCovered_sound`), produce the response segment chains (joint cases
→ pieces; the four reposition cases → frozen-left segments). Self-loop staying is backed
by the declared self-edges (VERIFIED 2026-07-15: every benchmark mode declares itself in
`next` — add the per-benchmark `decide` check; no automaton change needed).
**Gate:** `theorem3_faithful_multi{,_reposition}` restated without any Emit* hypothesis;
rover_drag pilot re-based on it; axioms unchanged.

## R2 — statement conditioning (the code's quantification)
Entry conditioning = `admissible` (SAT `guardL ∧ guardR ∧ inv`; the ∀ ranges over these),
`mv = q0`, σ = preJ; left family = ALL modes' windows, each `test(guardL)`-gated at entry.
**Gate:** top theorem's start set provably matches `coverMode`'s admissible-start ∀; a
watertank-shaped 3-mode toy goes through where it previously demanded phantom pairs.

## R3 — canonical ϕinv + encoding identity
Builder from the lowered invariant component(s) + generic `encode … = invLe g` proof.
Kills the `hψ`/`hinvL`/`hinvR` residuals.
**Gate:** pilot instance carries NO encoding hypotheses.

## R4 — multi-component invariants (the full `ϕ_rel`)
The tool certifies ALL components (`invComponents`): per-component queries via THREE
routes (A domain / B strict / C superlevel), each component's domain narrowed by the
OTHER components ≤ 0 (multi-barrier coupling) and the checked cuts. Mechanization must
match: per-component certificates, per-route adapters (route A exists =
`segPres_from_flowCert`; B/C partially — `DISuperlevel`), and the multi-barrier
simultaneous-preservation lemma (verify existing or build).
**Gate:** a multi-component benchmark's full conjunction invariant certified, not just
the primary component.

## R5 — emission door + instance battery
`--emit-cover`: per benchmark per left mode emit λ, `bBudget`, node flags, edges +
pruned bits, admissible starts, and the query/verdict list — drift-checked Lean literals
(EmitIR pattern). Generator script writes instances: real-systems graph, `CoverCert`
from named verdicts, `decideCovered` re-run in kernel, bridge applied.
**Gate:** all 46 tool-certified benchmarks build with axioms exactly
`[propext, Classical.choice, Quot.sound, z3_unsat_sound]`; suite + drift + trust audits
green. Any benchmark that refuses = a logged code-or-proof finding, triaged before
proceeding.

## R6 — viability certificates (retire the last analytic hypothesis)
New tool query family: per mode, per evolve-box face, `UNSAT(on-face ∧ field-outward)`
(forward-invariance); one generic Picard lemma (compact box + forward-invariance +
polynomial field ⟹ solutions exist for all needed durations). Adapter feeds the
extraction from R1.
**Gate:** viability hypotheses removed on every mode whose face-queries pass; legitimate
failures fall back to a named per-mode single-system hypothesis (documented per
benchmark) or a model-margin fix — the tool-improvement loop.

## R7 — closure
Retire `ClockedTop` cadenced chain + `GBoxAll` to Archive; README + Trusted/README
restated against the frozen contract; ASSET-MAP refreshed; suite regression.
**Gate:** `#print axioms` battery = the four axioms everywhere; hypothesis list in docs
matches the frozen contract verbatim.

## R7 closure record (2026-07-16)

Decision (b): the cadenced chain is DEPRECATED, not deleted — the 46/46 `_real`
settling battery stays green on it until the reposition-window modal form and the
13-benchmark cut lift reach parity; then chain + cadenced demos retire to `Archive/`
in one commit. `Instances/EndToEnd.lean` carries the deprecation header;
`Proofs/Encoding/ClockedTop.lean`'s header note is DEFERRED to the next
battery-invalidating batch (rebuild hygiene: a comment edit there cascades through
`FvDischarge` into the full battery re-elaboration). `GBoxAll` retains its
quarantine notice. Rule: never delete a theorem before its stronger replacement
exists; never trigger a battery rebuild for a comment.

## Standing discipline
- Before building anything: check docs/ASSET-MAP.md; update it when a top theorem lands.
- Any tool↔proof mismatch: stop, record in COVER-AUDIT.md, resolve BY THE CODE or flag
  the tool fix to the user. Never invent parallel structures.
- Bank-when-green: commit + push at every gate.

## S-arc record (2026-07-16, autonomous session)

**S1 LANDED** (f637677): `watertank_modal` — multi-mode `rvalid (theorem3Form …)` with
static reposition hops along declared edges, envelope-carrying `phiInvE` via the
LR-split relational envelope (`envLR`), six per-pair route verdicts (`VerdW`) + six
ENVELOPE-CONDITIONED existence residuals (`ESW`, S3's target). Axioms exactly the four.
Negative findings: `Hmulti_window_prefixed` is unusable for nonempty hop lists (its
`hdisH` is unsatisfiable — frozen hops bind every left coordinate; k = 1 route
`Hmulti_window1_prefixed` added instead); `hostComps = [gW]` kernel identity blocked by
`String.startsWith` (single-component verdicts stated over `[gW]` directly — same query
shape). Deferred: rover_drag pilot re-conditioning onto the E-chain; modal-instance
generator.

**S2 proof layer LANDED** (7f56d3e, 532a454): `CutCover.lean` (RightReachG —
guard-triggered switching recorded at each switch, the assumption the tool's O1 already
makes; `CoverCertMC`; `pres_multi_cut` — the cut baton: left atoms enter once per window
and persist, right atoms re-enter at switches; `check_sound_multi_cut`) +
`CutCoverDischarge.lean` (`hostAtom_iff`, `hostGuard_cutAtoms_sat` O1 at getD level,
`atomsStay_L_frozen_dyn`). Key recon: the one-sided O2 probes cover BOTH the joint and
the frozen-left dynamic flows (left atoms frozen, right atoms same-verdict), so NO new
tool query kind is needed for staying; O1 guard-lowering-success facts are provable by
`simp [IR, lowerF, lowerE, resolveVar, parseRat, findIdx?, findIdx?.go]` + `decide`
(verified on arm_chain_rung3). REMAINING (mechanical): per-benchmark instance generator
(gen_throughout pattern with narrowed strata-verdict hypotheses over
`dom ∧ cutF cutL ∧ cutF (cutR q)`, per-atom O2 verdict hypotheses routed to
`atom_boxle_*`, `Gd q := hostGuard Side.R (mR q)`, atoms from `EvolStrengthenings`) +
the 13 instances (serial builds for the 12-dof files) + battery wiring. All 13 covers
use repositions — the baton's reposition cases are exercised.

**S3 pending**: bounded-time viability + wiring into the `hES`/`ESW` residuals.
**S4 pending**: no battery-invalidating rebuild occurred this session; the batch
(invComponents decoupling, ClockedTop header) still waits for the first unavoidable one.

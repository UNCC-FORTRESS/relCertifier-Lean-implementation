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

## Standing discipline
- Before building anything: check docs/ASSET-MAP.md; update it when a top theorem lands.
- Any tool↔proof mismatch: stop, record in COVER-AUDIT.md, resolve BY THE CODE or flag
  the tool fix to the user. Never invent parallel structures.
- Bank-when-green: commit + push at every gate.

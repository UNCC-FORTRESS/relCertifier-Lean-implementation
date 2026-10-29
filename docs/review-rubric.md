# Benchmark review rubric (relCertifier suite_v2, branch benchmark-fixes, tip 4c47fd4)

Repo: /Users/jxiang1/Develop/relCertifier-lean-implementation (READ ONLY: do not edit, build, or run the tool; do not use git write commands).
For each benchmark read benchmarks/suite_v2/<name>/input.txt in full (header comments + model), and the benchmark's row in docs/paper-numbers/matrix.md (grep the name) for verdict, timing, mechanism cells and cover shape. Consult docs/SUITE-REDESIGN.md only where the header points to a section.

Score each benchmark on three axes, integers 1-5 (5 = exemplary, 3 = acceptable, 1 = should be fixed or dropped):

P  Physical model. Are dynamics, units, domains, guards and modes those of a real plant/controller? Domains must be physical limits (ranges, capacities), never bounds that force the property. Mode structure must correspond to a real controller behavior (bands, fallbacks, phases), guards must be reachable, and the left/right pair must be a real scenario (sensor attack, degraded controller, model refinement, DoS, miscalibration...). Deduct for ad hoc constants, unit mismatches, modes that can never be entered, or domains tuned to the claim.

R  Relational property. Is the declared invariant a claim someone would care about (robustness tolerance, refinement slack, non-interference bound)? Is it non-trivial: not implied by the domains alone, not vacuous, with the tolerance either tight (header gives evidence: smaller tolerance declined/refuted) or justified by a stated requirement? Does the direction make sense (which side is universally quantified)? Deduct for tolerances that are loose without justification, properties implied by bounds, or witnesses that trivially copy the left.

C  Clarity/faithfulness. Header states the scenario, every deviation from a source (literature) or from physics, the tight-bound evidence, and the mechanisms claimed; the mechanism cells in matrix.md agree with the header.

Then an overall 1-5 (not an average: the weakest axis dominates) and a verdict: KEEP / POLISH (header or constant fix) / RETHINK (model or property change) / DROP.

Output: write ONE markdown file at the path given in your prompt, with
1. a table: | benchmark | P | R | C | overall | verdict | one-line reason |
2. per benchmark, 3-6 lines: what the model is (one sentence), what the property says in words, the strongest concern (or "none"), and a concrete fix if verdict is not KEEP.
Be specific and skeptical; cite the header line or constant you object to. Do not pad. Then report back in under 15 lines: the table rows only.

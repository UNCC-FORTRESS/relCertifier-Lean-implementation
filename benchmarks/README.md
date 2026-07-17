# Benchmark suite

One directory per benchmark; `input.txt` is the complete specification in the
certifier's DSL:

* `vars` — the shared state-variable table (both sides use the same names);
* `L:` / `R:` — the ideal and implementation automata: per mode `odes` (polynomial
  right-hand sides), `guard` (entry condition), `evolve` (domain the flow may not
  leave), `next` (declared successors);
* `invariant` — per left mode, the relational invariant over `L_`/`R_`-prefixed
  variables (e.g. `L_x <= R_x + 3`);
* `lambda` — the admissible time-stretch range for the right's responses.

`relcert <dir>/input.txt` parses, lowers, searches, and certifies. Certified
benchmarks' data is emitted into `RelCertifier/Instances/Bench*.lean` (drift-checked
literals) from which the per-benchmark theorem instances are generated — see the
repository README's "File guide". The suite (47): watertank; arm chain/fidelity and
plant fan families; rover refinement ladders (2–12 dof); dof-terrain rungs; endurance,
attitude, rollover stories.

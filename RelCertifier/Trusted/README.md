# Trusted/ — the audit surface

Everything the kernel cannot check lives in this folder. An auditor who reads these seven
files (plus the Lean kernel and Z3 itself) has read the entire trust base:

| file | trusted content |
|---|---|
| `Parse.lean` | the strict parser: `input.txt` text ↦ `PProblem` IR. Reject-never-weaken; what it accepts *defines* what the theorems are about. |
| `EmitIR.lean` | the emission door: prints the parsed IR as the Lean literals in `Instances/BenchIR.lean` (drift is caught by the ir-drift test, but the printer itself is trusted). |
| `Smt.lean` | the SMT **printer** (`toScript`): Lean `IForm` queries ↦ SMT-LIB text. The IR→host mirror lemmas in the same file are kernel-checked; only the printer is trusted. |
| `Z3.lean` | the Z3 process session (IO). |
| `Oracle.lean` | **the one axiom**: `z3_unsat_sound : z3solve q = unsat → ∀ σ, ¬ sat q σ`, realized by the printer + Z3. Everything above it is a theorem. |
| `Run.lean` | the lowering `PProblem → IR` (`lowerE`/`lowerF`/`dynOf`) and batch IO glue. Total, structural, kernel-reducing — its *outputs* are re-certified where possible (Faithful, CutCerts), but the lowering semantics is part of the claim. |
| `OracleAPI.lean` | the tool's search: query budgets, the checked-cut O1/O2 search, segment/cover orchestration (IO). Its *outputs* are certified (`cutCertWF` by `rfl`, verdicts through `z3_unsat_sound`); the search itself is untrusted and cannot affect soundness — only completeness. |

**The claim.** If the parser accepts the benchmark, the printer prints the queries
faithfully, and Z3's `unsat` verdicts are correct, then every theorem in `Proofs/` and
`Instances/` holds as stated, checked by the Lean kernel with axioms
`[propext, Classical.choice, Quot.sound]` plus `z3_unsat_sound` exactly at the Z3 leaves.

**Import discipline** (checked by `scripts/trust_audit.py`): files in this folder may
import each other, `Core/`, `Checker/` (pure, kernel-cited definitions), and upstream
packages — never `Proofs/`, `Instances/`, or `Archive/`.

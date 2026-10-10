# Trusted/ — the audit surface

Everything the kernel cannot check lives in this folder. An auditor who reads the files
below (plus the Lean kernel and Z3 itself) has read the entire trust base; the rest of this
folder is untrusted search or IO glue whose outputs are re-checked.

| file | role | trusted? |
|---|---|---|
| `Parse.lean` | the strict parser: `input.txt` text ↦ `PProblem` IR. Reject-never-weaken; what it accepts *defines* what the theorems are about | **trusted** |
| `KeyAudit.lean` | the CLI gate: refuses inputs with sections or keys the parser does not consume (`max_depth`, `bound_T` whitelisted, read by no stage) | **trusted** (it can only refuse) |
| `Run.lean` | the lowering `PProblem → SMT-IR` (`lowerE`/`lowerF`/`dynOf`/`invToG`), the segment parts, the stratified domain, the three route queries, the λ grid | **trusted**: its outputs are quoted by the kernel instances by `rfl`, but what the lowering *means* is part of the claim |
| `Smt.lean` | the SMT **printer** (`toScript`): `IForm` queries ↦ SMT-LIB text. The IR→host mirror lemmas in the same file are kernel-checked; only the printer is trusted | **trusted** |
| `Oracle.lean` | **the one axiom**: `z3_unsat_sound : z3solve q = unsat → ∀ σ, ¬ sat q σ`, realized operationally by the printer + Z3 | **trusted** |
| `Z3.lean` | the Z3 process session: pinned binary, `(reset)` before every query, per-query timeout (10 s) and rlimit (64 000 000); `unknown`/errors are never verdicts | **trusted** (IO) |
| `EmitIR.lean` | `--emit-ir`: prints the parsed IR as the Lean literals the instances quote (`InstancesV2/BenchIR/`); drift is caught by `relcert-test` `[ir-drift-v2]`, the printer itself is trusted | **trusted** |
| `JointVars.lean`, `InvComponents.lean` | the joint variable list; the multi-component invariant lowering | part of the lowering |
| `Handoff.lean`, `NonConnQuery.lean` | the handoff and non-connection queries, defined once at the SMT-IR level so the certifier, the runner and the kernel bridge (`ModeHandoff.handoff_of_unsat`, `NonConnBridge.nonconn_of_unsat`) cannot drift | part of the lowering |
| `OracleAPI.lean` | the certifier `certify`: checked-cut search, non-connection pruning, per-left-mode cover search (joint segments, dynamic right-only reposition), budgets; `--emit-cover`/`--emit-viability` | **untrusted**: its outputs are re-checked (cover replay by `decide`, cut well-formedness by `rfl`, verdicts through `z3_unsat_sound`) |
| `ViabilityEmit.lean` | `--emit-viability2/3`: per-face viability tags | **untrusted** (emitter) |

**The claim (the frozen hypothesis contract).** If the parser accepts the benchmark, the
lowering means what it says, the printer prints the queries faithfully, and Z3's `unsat`
verdicts are correct, plus the model-faithfulness assumptions of the transition semantics
(successor-completeness with guard-gated switching: every mode change of the right system
moves it into a declared successor mode, and at that instant the state satisfies the
entering mode's guard; and the paper's Assumption 1, nonblocking right flows), then every
theorem of `InstancesV2/BatteryV2.lean` holds as stated, checked by the Lean kernel with
axioms `[propext, Classical.choice, Quot.sound]` plus `z3_unsat_sound` exactly at the Z3
leaves. Nothing else is assumed: the tool's cover decisions are re-decided in the kernel
(`InstancesV2/CoverReplay.lean`, all 45), the cut certificates are kernel-checked well
formed (`InstancesV2/Cuts/`, all 45), and every `Verd` hypothesis is pinned to the query
the runner sends (`VerdictsV2/`, `Verdicts/`).

**Import discipline** (checked by `scripts/trust_audit.py`): files in this folder may
import each other, `Core/`, `Checker/` (pure, kernel-cited definitions), and upstream
packages; never `Proofs/` or `Instances*/`.

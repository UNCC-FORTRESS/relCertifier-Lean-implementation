/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The declared coverage counts, checked against the tables that generate them

`Verdicts/Coverage.lean` declares how many hypotheses a green `--run-verdicts` owes, and
the runner fails if it issues fewer. That guard is what makes a run which quietly skipped
work distinguishable from one that did it all — but the numbers themselves were typed by
hand, and nothing checked them.

The failure mode is a habit rather than a code path. Add a benchmark, watch the run fail
on the count, and paste in whatever the run just produced: the guard is now a rubber
stamp, and it looks exactly like a legitimate update.

This file removes that. Each phase's total is *also* derived from the table that
generates the work — for the modal phase, mode pairs × components per row; for the cut
phase, tagged atoms per side per benchmark — and the derived value is proved equal to the
declared one. So the two can only be changed together:

* change the table without updating `Coverage.expected` → this file fails to compile;
* update `Coverage.expected` to match a run without changing the table → same;
* runner issues a different number than either → `--run-verdicts` fails at runtime.

Three-way agreement: what the tables describe, what we declared, and what was actually
sent to Z3. (The fixed six-query `watertank` phase left with the `watertank` modal
theorem on 2026-10-09, when the benchmark was DECLINED after the static-reposition
removal.)
-/
import RelCertifier.Verdicts.ModalTablePins
import RelCertifier.Verdicts.RunCut
import RelCertifier.Verdicts.RunHandoff
import RelCertifier.Verdicts.RunNonConn

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.ModalSpecs

/-- What the modal phase owes, read off `modalTable`: for each row, the number of mode
pairs the runner visits times the number of components it checks per pair (the invariant
components in `order`, plus any ceiling head, region head or tail face). -/
def derivedModal : ℕ :=
  modalTable.foldl (fun acc r =>
    let (spec, info, order) := r
    let heads := (if info.ceilCo.isSome then 1 else 0)
               + (if info.region.isSome then 1 else 0)
               + (if info.tailCo.isSome then 1 else 0)
    acc + (modalPairs spec info).length * (order.length + heads)) 0

/-- What the cut phase owes: one probe per tagged cut atom, on each side, per benchmark. -/
def derivedCut : ℕ :=
  cutBenchmarks.foldl (fun acc r =>
    match benchIRTable.find? (fun q => q.1 == r.1) with
    | some (_, p) =>
        acc + (modeAtoms Side.L r.2.L p.L.modes).length
            + (modeAtoms Side.R r.2.R p.R.modes).length
    | none => acc) 0

/-- The modal total is not a number someone remembered — it is what `modalTable` says. -/
theorem derivedModal_eq_expected : derivedModal = expected.modal := by decide

/-- Likewise for the cut probes, against `cutBenchmarks` and the emitted IR. -/
theorem derivedCut_eq_expected : derivedCut = expected.cut := by decide

/-- What the handoff phase owes: one query per declared left transition of every certified
benchmark — the resolved pairs `Handoff.transitions` the runner actually visits. -/
def derivedHandoff : ℕ :=
  certifiedIRTable.foldl (fun acc r => acc + (Handoff.transitions r.2).length) 0

/-- The handoff total is what the emitted IR declares, not a remembered number. -/
theorem derivedHandoff_eq_expected : derivedHandoff = expected.handoff := by decide

/-- Every declared-failing handoff names a benchmark in the table and a transition it
really declares — a stale entry (a renamed benchmark, a removed edge) fails the build
rather than being silently "expected" forever. -/
theorem expectedHandoffFailures_declared :
    expectedHandoffFailures.all (fun f =>
      match benchIRTable.find? (fun r => r.1 == f.1) with
      | some (_, p) => (Handoff.transitions p).contains (f.2.1, f.2.2)
      | none => false) = true := by decide

/-! ## The non-connection phase -/

/-- What the non-connection phase owes in edges: the pruned pairs the emitted covers
record, summed over the cover table the runner walks. -/
def derivedPruned : ℕ :=
  benchCoverTable.foldl (fun acc c => acc + c.2.pruned.length) 0

/-- The declared pruned-edge count is what the emitted covers say. -/
theorem derivedPruned_eq_expected : derivedPruned = expected.prunedEdges := by decide

/-- Two queries per pruned edge: the declared query count is tied to the edge count. -/
theorem nonconn_eq_two_pruned : expected.nonconn = 2 * expected.prunedEdges := by decide

/-- The cover table walks exactly the certified benchmarks, in the same order as the IR
table the queries are rebuilt from — a cover row for a benchmark with no IR (or a
missing cover, or a cover for a declined benchmark) fails here, not at runtime. -/
theorem benchCoverTable_names :
    benchCoverTable.map (·.1) = certifiedIRTable.map (·.1) := by decide

/-- Every pruned pair names a declared right edge of its benchmark's IR: the source and
target are right modes and the target is in the source's `next` list. A stale pair (a
renamed mode, a removed edge) fails the build rather than being re-run forever. -/
theorem prunedEdges_declared :
    prunedEdges.all (fun e =>
      match benchIRTable.find? (fun r => r.1 == e.1) with
      | some (_, p) =>
          match p.R.modes.find? (·.name == e.2.1), p.R.modes.find? (·.name == e.2.2) with
          | some mR, some _ => mR.next.contains e.2.2
          | _, _ => false
      | none => false) = true := by decide

/-- Every pruned edge's two queries rebuild from the emitted data (so the runner never
reaches its `did not rebuild` branch on the current suite): the successor guard is a
strict scalar threshold and every part lowers. -/
theorem prunedEdges_rebuild :
    prunedEdges.all (fun e =>
      match benchIRTable.find? (fun r => r.1 == e.1),
            benchCutsTable.find? (fun r => r.1 == e.1) with
      | some (_, p), some (_, cuts) => (nonConnQueriesOf p cuts e.2.1 e.2.2).isSome
      | _, _ => false) = true := by decide

end RelCertifier.Verdicts

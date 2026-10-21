/-
The strict demo's verdict run: the strict query groups (`bridgeGroupsS`) of
`benchmarks/strict_demo/watertank_strict`, sent to Z3 by the bridge runner's own per-benchmark
loop (`VerdictsV2.runBridgeBench`), at the instance's dimension. Every group discharged is the
hypothesis `hok : GroupsOK gs` of `watertank_strict_bridge_run` (and, through
`verdictsS_of_groups`, `VerdictsS`).

Run: lake env lean scripts/strict_demo_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge
import RelCertifier.InstancesV2.Bridge.WatertankStrict

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted

def demoRec : BridgeRec :=
  ⟨"watertank_strict", 2 + 1, Bridge.WatertankStrict.IR, Bridge.WatertankStrict.cX,
    Bridge.WatertankStrict.cov, Bridge.WatertankStrict.prog, Bridge.WatertankStrict.ce⟩

def runDemo : IO Unit := do
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      let (ok, k) ← runBridgeBench s demoRec
      s.close
      IO.println s!"  [strict demo] {k} groups, {if ok then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"

#eval runDemo

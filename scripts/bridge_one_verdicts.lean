/-
The bridge verdicts of ONE suite benchmark (`docs/HYP-SLICING.md`): the groups of
`bridgeGroupsS` of the named benchmark, sent to Z3 by the bridge runner's own per-benchmark
loop (`VerdictsV2.runBridgeBench`) at the knob of the environment (`RELCERT_SLICE_HOPS`).
Every group discharged is the hypothesis `hok : GroupsOK gs` of `<b>_bridge_run`.

Run: RELCERT_BRIDGE_ONE=<bench> [RELCERT_SLICE_HOPS=k] lake env lean scripts/bridge_one_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted

def runOne : IO Unit := do
  let b := (← IO.getEnv "RELCERT_BRIDGE_ONE").getD "watertank"
  let k ← sliceHopsFromEnv
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      let (ok, n) ← runBridgeBench s k (suiteRecV2 b)
      s.close
      IO.println s!"  [bridge one] {b} hops={k}: {n} groups, {if ok then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"

#eval runOne

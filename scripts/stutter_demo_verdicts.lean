/-
The stutter demo's verdict run: the query groups (`bridgeGroups`) of
`benchmarks/stutter_demo/salt_tank_stutter`, sent to Z3 at the instance's dimension, each group
discharged by its first `unsat` member, as the bridge runner does (`VerdictsV2.runBridgeBench`).
Every group discharged is the hypothesis `hok : GroupsOK gs` of `salt_tank_stutter_bridge_run`
(and, through `verdicts_of_groups`, `Verdicts`).

Run: lake env lean scripts/stutter_demo_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge
import RelCertifier.InstancesV2.Bridge.SaltTankStutter

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted

def runDemo : IO Unit := do
  let p := Bridge.SaltTankStutter.IR
  let n := 3 + 1
  let coord := fun (i : Fin n) => p.L.stateVars.getD i.val s!"pad{i.val}"
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      match bridgeGroups p n Bridge.SaltTankStutter.cX Bridge.SaltTankStutter.cov
          Bridge.SaltTankStutter.prog Bridge.SaltTankStutter.ce with
      | none => IO.println "  [stutter demo] the query groups did not rebuild"
      | some gs =>
        let mut bad := 0
        for g in gs do
          let mut hit := false
          for q in g do
            if !hit then
              match ← s.check (q.toScript coord) with
              | .ok .unsat => hit := true
              | _ => pure ()
          if !hit then bad := bad + 1
        s.close
        IO.println s!"  [stutter demo] {gs.length - bad}/{gs.length} groups, {if bad == 0 then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"

#eval runDemo

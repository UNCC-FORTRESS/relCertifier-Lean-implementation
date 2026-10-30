/-
The pre-landing demo's verdict run: the query groups (`bridgeGroupsPL`) of
`benchmarks/prelanding_demo/engine_cooling_prelanding`, sent to Z3 at the instance's dimension,
each group discharged by its first `unsat` member, as the bridge runner does
(`VerdictsV2.runBridgeBench`). Every group discharged is the hypothesis `hok : GroupsOK gs` of
`engine_cooling_prelanding_bridge_run` (and, through `verdictsPL_of_groups`, `VerdictsPL`).
Also counts the pre-landing groups alone (the `dynGroupsPL` part).

Run: lake env lean scripts/prelanding_demo_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge
import RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted

def runDemo : IO Unit := do
  let p := Bridge.EngineCoolingPrelanding.IR
  let n := 3 + 1
  let coord := fun (i : Fin n) => p.L.stateVars.getD i.val s!"pad{i.val}"
  let cX := Bridge.EngineCoolingPrelanding.cX
  let covM := Bridge.EngineCoolingPrelanding.covM
  let prog := Bridge.EngineCoolingPrelanding.prog
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      let dyn := (List.range (nL p)).flatMap (fun l => (List.range (nR p)).flatMap (fun q =>
        [true, false].flatMap (fun pre =>
          ((dynGroupsPL p n cX covM prog l q pre).getD []))))
      IO.println s!"  [prelanding demo] {dyn.length} pre-landing groups (3 routes each)"
      match bridgeGroupsPL p n cX covM prog Bridge.EngineCoolingPrelanding.ce with
      | none => IO.println "  [prelanding demo] the query groups did not rebuild"
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
        IO.println s!"  [prelanding demo] {gs.length - bad}/{gs.length} groups, {if bad == 0 then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"

#eval runDemo

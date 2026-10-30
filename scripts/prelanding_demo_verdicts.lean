/-
The pre-landing demos' verdict run: the query groups of
`benchmarks/prelanding_demo/engine_cooling_prelanding` (`bridgeGroups`, non-strict rows) and
`benchmarks/prelanding_demo/hold_reposition_strict` (`bridgeGroupsS`, a strict row), each on the
cover merged with its pre-landing record, sent to Z3 at the instance's dimension, each group
discharged by its first `unsat` member, as the bridge runner does (`VerdictsV2.runBridgeBench`).
Every group discharged is the hypothesis `hok : GroupsOK gs` of the instance's `_bridge_run`.
Also counts the reposition groups alone (`dynGroups`, on each node's region).

Run: lake env lean scripts/prelanding_demo_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge
import RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
import RelCertifier.InstancesV2.Bridge.HoldRepositionStrict

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted

def runGroups (tag : String) (p : Parse.PProblem) (dyn : Nat)
    (ogs : Option (List (List (IForm (3 + 1))))) : IO Unit := do
  let n := 3 + 1
  let coord := fun (i : Fin n) => p.L.stateVars.getD i.val s!"pad{i.val}"
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      IO.println s!"  [{tag}] {dyn} reposition groups (on the nodes' regions)"
      match ogs with
      | none => IO.println s!"  [{tag}] the query groups did not rebuild"
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
        IO.println s!"  [{tag}] {gs.length - bad}/{gs.length} groups, {if bad == 0 then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"

def dynCount (p : Parse.PProblem) (cX : Oracle.EvolStrengtheningX) (covM : CoverEmitE)
    (prog : Progress.ProgressEmitE) : Nat :=
  ((List.range (nL p)).flatMap (fun l => (List.range (nR p)).flatMap (fun q =>
    [true, false].flatMap (fun pre => ((dynGroups p (3 + 1) cX covM prog l q pre).getD []))))).length

def runDemos : IO Unit := do
  runGroups "prelanding demo, engine cooling" Bridge.EngineCoolingPrelanding.IR
    (dynCount Bridge.EngineCoolingPrelanding.IR Bridge.EngineCoolingPrelanding.cX
      Bridge.EngineCoolingPrelanding.covM Bridge.EngineCoolingPrelanding.prog)
    (bridgeGroups Bridge.EngineCoolingPrelanding.IR 4 Bridge.EngineCoolingPrelanding.cX
      Bridge.EngineCoolingPrelanding.covM Bridge.EngineCoolingPrelanding.prog
      Bridge.EngineCoolingPrelanding.ce)
  runGroups "prelanding demo, strict row" Bridge.HoldRepositionStrict.IR
    (dynCount Bridge.HoldRepositionStrict.IR Bridge.HoldRepositionStrict.cX
      Bridge.HoldRepositionStrict.covM Bridge.HoldRepositionStrict.prog)
    (bridgeGroupsS Bridge.HoldRepositionStrict.IR 4 Bridge.HoldRepositionStrict.cX
      Bridge.HoldRepositionStrict.covM Bridge.HoldRepositionStrict.prog
      Bridge.HoldRepositionStrict.ce)

#eval runDemos

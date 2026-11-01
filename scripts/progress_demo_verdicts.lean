/-
The mixed-shape progress demo's verdict run (`benchmarks/progress_demo/stopline_friction_mixed`,
docs/PRELANDING.md "Two-stage certificates in every direction").

1. The query groups (`bridgeGroups`) of the demo on the cover merged with its pre-landing record
   (`covM`), sent to Z3 at the instance's dimension, each group discharged by its first `unsat`
   member, as the bridge runner does (`VerdictsV2.runBridgeBench`). Every group discharged is the
   hypothesis `hok : GroupsOK gs` of `stopline_friction_mixed_bridge_run`.
2. Adversarial certificates: each emitted helper-up / landing-down certificate mutated so that
   the helper does not hold (helper direction flipped, helper threshold above the brake's target
   3, helper rate too high) or the landing stage does not reach the guard (landing threshold
   0.5 > 0.35, landing direction flipped, landing rate too high). Each mutant replaces the
   certificate in the record; the run must then leave some group undischarged (DECLINED: the
   hypothesis `GroupsOK` of the bridge theorem is not available), while the mutant still passes
   the kernel's shape gate (`certOK`, so the decline is the queries', not the shape's).
3. The shape gate itself: a three-stage certificate fails `certOK` (decided by `#eval`).

Run: lake env lean scripts/progress_demo_verdicts.lean
-/
import RelCertifier.VerdictsV2.RunBridge
import RelCertifier.InstancesV2.Bridge.StoplineFrictionMixed

open RelCertifier RelCertifier.VerdictsV2 RelCertifier.Emitted RelCertifier.Progress

namespace ProgressDemo

abbrev IR := Bridge.StoplineFrictionMixed.IR
abbrev cX := Bridge.StoplineFrictionMixed.cX
abbrev covM := Bridge.StoplineFrictionMixed.covM
abbrev prog := Bridge.StoplineFrictionMixed.prog
abbrev ce := Bridge.StoplineFrictionMixed.ce

/-- The emitted certificates of the mixed shape (two stages, helper up, landing down). -/
def isMixed (c : ProgressE) : Bool :=
  match c.stages with
  | [h, l] => h.up && !l.up
  | _ => false

/-- The mutants of a mixed certificate, with their names. -/
def mutants (c : ProgressE) : List (String × ProgressE) :=
  match c.stages with
  | [h, l] =>
    [("helper direction flipped", { c with stages := [{ h with up := false }, l] }),
     ("helper threshold 7/2 above the target 3", { c with stages := [{ h with theta := 7/2 }, l] }),
     ("helper rate 100", { c with stages := [{ h with rate := 100 }, l] }),
     ("landing threshold 1/2 above the guard 7/20", { c with stages := [h, { l with theta := 1/2 }] }),
     ("landing direction flipped", { c with stages := [h, { l with up := true }] }),
     ("landing rate 100", { c with stages := [h, { l with rate := 100 }] })]
  | _ => []

/-- The record with certificate number `i` replaced by `c'`. -/
def replaceAt (i : Nat) (c' : ProgressE) : ProgressEmitE :=
  { prog with certs := prog.certs.set i c' }

/-- The right-mode index of a certificate (the shape gate's `q`). -/
def qOf (c : ProgressE) : Nat := modeIdx IR.R.modes c.mR

/-- Discharge the groups: the number discharged and the total. -/
def runGroups (s : Z3Session) (gs : List (List (IForm 4))) : IO (Nat × Nat) := do
  let coord := fun (i : Fin 4) => IR.L.stateVars.getD i.val s!"pad{i.val}"
  let mut bad := 0
  for g in gs do
    let mut hit := false
    for q in g do
      if !hit then
        match ← s.check (q.toScript coord) with
        | .ok .unsat => hit := true
        | _ => pure ()
    if !hit then bad := bad + 1
  pure (gs.length - bad, gs.length)

def runDemo : IO Unit := do
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3: {e}"
    | .ok s =>
      let nMixed := (prog.certs.filter isMixed).length
      IO.println s!"  [progress demo] {prog.certs.length} certificates, {nMixed} of the mixed shape (helper up, landing down)"
      IO.println s!"  [progress demo] kernel gate progOK on the merged cover: {progOK IR 4 covM prog}"
      match bridgeGroups IR 4 cX covM prog ce with
      | none => IO.println "  [progress demo] the query groups did not rebuild"
      | some gs =>
        let (ok, tot) ← runGroups s gs
        IO.println s!"  [progress demo] {ok}/{tot} groups, {if ok == tot then "ALL DISCHARGED" else "NOT ALL DISCHARGED"}"
      -- the adversarial certificates
      let mut declined := 0
      let mut total := 0
      for (c, i) in prog.certs.zipIdx do
        if isMixed c then
          for (nm, c') in mutants c do
            total := total + 1
            let prog' := replaceAt i c'
            let shape := certOK IR 4 covM (qOf c') c'
            match bridgeGroups IR 4 cX covM prog' ce with
            | none =>
              declined := declined + 1
              IO.println s!"    mutant {c.mL}/{c.mR} pre={c.pre} [{nm}]: groups do not rebuild, DECLINED (certOK {shape})"
            | some gs =>
              let (ok, tot) ← runGroups s gs
              if ok < tot then declined := declined + 1
              IO.println s!"    mutant {c.mL}/{c.mR} pre={c.pre} [{nm}]: {ok}/{tot} groups, {if ok < tot then "DECLINED" else "NOT DECLINED"} (certOK {shape})"
      IO.println s!"  [progress demo] adversarial certificates: {declined}/{total} DECLINED"
      s.close
      -- the shape gate: three stages are rejected in the kernel's gate
      match prog.certs.find? isMixed with
      | some c =>
        let c3 := { c with stages := c.stages ++ c.stages.take 1 }
        IO.println s!"  [progress demo] a three-stage certificate passes certOK: {certOK IR 4 covM (qOf c3) c3}"
      | none => IO.println "  [progress demo] no mixed certificate"

end ProgressDemo

#eval ProgressDemo.runDemo

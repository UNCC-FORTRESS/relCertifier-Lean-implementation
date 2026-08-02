/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The modal verdict runner — one route for every theorem's hypotheses

Before this, hypotheses were discharged two ways: `Verdicts/Run.lean` re-ran
watertank's six and `Verdicts/RunCut.lean` the 105 cut probes, while the remaining
modal instances' packs were left to "the tool's own certification run" — a coarse
`CERTIFIED` line with no per-hypothesis output and no pin tying it to the theorem.
That split is what let six vacuous theorems sit unnoticed until the 2026-07-31
audit (`docs/VERDICT-EVIDENCE-AUDIT.md`).

This runner closes it. It walks `ModalSpecs.specs` — whose argument sets are tied
to the theorems by `modal_from_spec`, so they cannot drift — rebuilds each query
from the emitted IR through the same `Run.*` lowering the instances use, prints it
with the tool's own `toScript`, and reports Z3's verdict per hypothesis.

**It never falls back.** Anything it cannot rebuild is reported as `SKIP` with a
reason and makes the run non-green, so a gap is visible rather than silent.

`Verdicts/ModalPins.lean` proves the rebuilt query denotes the host-level term the
hypothesis names, so a green line here is evidence about the theorem's own query
and not about a lookalike.
-/
import RelCertifier.Verdicts.ModalPins
import RelCertifier.Verdicts.ModalVerd
import RelCertifier.Verdicts.GenericPins
import RelCertifier.Instances.ModalSpecs
import RelCertifier.Instances.BenchIR
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse RelCertifier.ModalSpecs

/-- What the runner needs beyond `VerdSpec` to rebuild an instance's queries:
the ambient dimension, the invariant row, λ, and the optional landing-mode region
(`some k` prepends `k − R₀`, the repaired `Hold` region). Every field is checked
against the instance by a `rfl` pin in `ModalSpecs` or by the audit's per-instance
pins; nothing here is inferred by pattern-matching source text. -/
structure RunInfo where
  /-- Ambient `Var n` dimension (may exceed the benchmark's state-variable count). -/
  dim     : ℕ
  /-- Which `invariants` row the instance's component terms come from. -/
  invRow  : ℕ := 0
  /-- λ numerator and denominator. -/
  lamN    : ℕ := 1
  lamD    : ℕ := 1
  /-- Landing-mode region constant `k`, prepending `k − R₀` (the repaired `Hold`
  region). -/
  region  : Option ℚ := none
  /-- Ceiling head `R_c − k_m` (or `k − R_c` when `ceilFlip`), per right mode. -/
  ceilCo  : Option ℕ := none
  ceilFlip : Bool := false
  ceilKs  : List ℚ := []
  /-- Same shape as the ceiling head, but appended *behind* the invariant's own
  components rather than prepended: `rover_rung2c` carries its mode region there, so
  the region is narrowed by the invariant instead of the other way round. -/
  tailCo  : Option ℕ := none
  tailFlip : Bool := false
  tailKs  : List ℚ := []
  /-- When the `Verd` takes one argument that is the LEFT index, the right mode is
  fixed at this value (and vice versa via `argIsRight`). -/
  fixedOther : Option ℕ := none
  argIsRight : Bool := false
  /-- Per-window λ, when the instance's λ depends on the left window. -/
  lamPerL : List (ℕ × ℕ) := []
  deriving Repr

/-- The `(left mode, right mode)` pairs a pack is checked at.

Factored out of `runSpec` so that `Verdicts/ModalTablePins.lean` can state, per
instance, which pairs the runner actually visits — a theorem about a transcription of
this code would not constrain the runner, so the runner must call the same function
the pins talk about. Getting this wrong is not hypothetical: `rover_rung2c` was being
checked at `(0, l)` instead of `(l, l)`, and `rover_drag` came out empty and was
checked at nothing at all. -/
def modalPairs (spec : VerdSpec) (info : RunInfo) : List (ℕ × ℕ) :=
  if spec.nullary then [(0, 0)]
  else if !spec.pairs.isEmpty then spec.pairs
  else spec.singles.map (fun v =>
    match info.fixedOther with
    | none   => (v, v)
    | some o => if info.argIsRight then (o, v) else (v, o))

/-! ### The pieces the runner builds, factored out

`ModalCodePins.lean` proves these denote the host-level terms the hypotheses name. The
functions have to be the ones `runSpec`/`checkComp` actually call — a lemma about a
transcription of this code would say nothing about what Z3 is asked. -/

/-- λ, as the runner builds it: the per-window entry if there is one, else `lamN/lamD`. -/
def modalLamI (info : RunInfo) (l n : ℕ) : ITerm n :=
  let (ln, ld) := info.lamPerL.getD l (info.lamN, info.lamD)
  .rat ((ln : ℚ) / (ld : ℚ))

/-- A `k − R_c` / `R_c − k` head from a coordinate, a flip flag and a per-mode constant
list. Shared by the ceiling head and the tail face, which differ only in where they sit
in the component list. -/
def modalHeadI (co : Option ℕ) (flip : Bool) (ks : List ℚ) (m : ℕ) {n : ℕ} (h : 0 < n) :
    List (ITerm n) :=
  match co with
  | none => []
  | some c =>
    let k : ℚ := ks.getD m (ks.getD 0 0)
    let v : ITerm n := .var (Rv ⟨c % n, Nat.mod_lt _ h⟩)
    [if flip then .bin .sub (.rat k) v else .bin .sub v (.rat k)]

/-- The three route queries tried per component, in order. -/
def modalRoutes {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n)
    (dom : IForm n) : List (String × IForm n) :=
  [("A", iflowQuery g fL fR lam dom), ("B", iflowQueryStrict g fL fR lam dom),
   ("C", iflowQuerySuperlevel g fL fR lam dom)]

/-- One hypothesis: all three routes on one component of one argument pair. -/
private def checkComp {n : ℕ} (s : Z3Session) (coord : Fin n → String)
    (g : ITerm n) (fL fR : Fin n → ITerm n) (lam : ITerm n) (dom : IForm n) :
    IO (Bool × String) := do
  let qs : List (String × IForm n) := modalRoutes g fL fR lam dom
  let mut detail := ""
  for (rn, q) in qs do
    match ← s.check (q.toScript coord) with
    | .ok .unsat => return (true, detail ++ s!"{rn}=unsat")
    | .ok .sat   => detail := detail ++ s!"{rn}=sat "
    | .ok v      => detail := detail ++ s!"{rn}={reprStr v} "
    | .error e   => detail := detail ++ s!"{rn}=err({e}) "
  pure (false, detail)

/-- Re-check every hypothesis of one instance. Returns `false` on any failure or
anything that could not be rebuilt. -/
def runSpec (s : Z3Session) (spec : VerdSpec) (info : RunInfo)
    (order : List ℕ) : IO Bool := do
  let some (_, p) := benchIRTable.find? (fun r => r.1 == spec.bench)
    | IO.println s!"  SKIP  {spec.bench}  (no emitted IR)"; return false
  let n := info.dim
  if h : 0 < n then
    let vars := p.L.stateVars
    let coord := fun (i : Fin n) => vars.getD i.val s!"pad{i.val}"
    let dm : PMode := ⟨"", [], .tt, .tt, []⟩
    let invF := (p.invariants.getD info.invRow ("", PForm.tt)).2
    let atoms := atomsOfM invF
    -- single-atom invariants are used whole by the instance; multi-atom ones are split
    let single := order.length == 1 && atoms.length == 1
    let base : List (ITerm n) := order.filterMap (fun i =>
      Run.invToG vars n (if single then invF else atoms.getD i .tt))
    if base.length != order.length then
      IO.println s!"  SKIP  {spec.bench}  (invariant lowering failed)"; return false
    let pairs := modalPairs spec info
    if pairs.isEmpty then
      IO.println s!"  SKIP  {spec.bench}  (no mode pairs to check)"; return false
    let mut ok := true
    for (l, m) in pairs do
      match Run.dynOf vars n Side.L (p.L.modes.getD l dm),
            Run.dynOf vars n Side.R (p.R.modes.getD m dm),
            Run.lowerF vars n Side.L (p.L.modes.getD 0 dm).evolve,
            Run.lowerF vars n Side.R (p.R.modes.getD 0 dm).evolve with
      | some fL, some fR, some dL, some dR =>
        -- the ceiling head is per right mode, so it is rebuilt inside the pair loop
        let ceilT : List (ITerm n) := modalHeadI info.ceilCo info.ceilFlip info.ceilKs m h
        -- the tail face is per right mode too, and sits behind the invariant's own
        let tailT : List (ITerm n) := modalHeadI info.tailCo info.tailFlip info.tailKs m h
        let comps : List (ITerm n) := ceilT ++ (match info.region with
          | none   => base
          | some k => (ITerm.bin .sub (.rat k) (.var (Rv ⟨0, h⟩))) :: base) ++ tailT
        let lam : ITerm n := modalLamI info l n
        for i in List.range comps.length do
          let dom := istrataDomHost (IForm.and dL dR) (comps.take i)
          let (good, detail) ← checkComp s coord (comps.getD i (.rat 0)) fL fR lam dom
          if good then
            IO.println s!"  UNSAT ({detail})  {spec.bench} (l={l},m={m}) comp={i}"
            counted
          else
            IO.println s!"  FAIL  {spec.bench} (l={l},m={m}) comp={i} : {detail}"
            ok := false
      | _, _, _, _ =>
        IO.println s!"  SKIP  {spec.bench} (l={l},m={m})  (field/domain lowering failed)"
        ok := false
    pure ok
  else
    IO.println s!"  SKIP  {spec.bench}  (dimension 0)"; return false

/-- Per-instance rebuild data, paired with the spec whose argument set is
kernel-tied to the theorem by `modal_from_spec`. -/
def modalTable : List (VerdSpec × RunInfo × List ℕ) :=
[
  (ArmChainRung1.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 0, lamPerL := [(5,2),(3,2),(1,1)] }, [0]),
  (ArmChainRung2.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 1, lamPerL := [(7,4),(5,4),(1,1)] }, [0]),
  (ArmChainRung3.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, region := some (3/5), fixedOther := some 3 }, [0]),
  (ArmFidelityHigh.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, region := some (3/5), fixedOther := some 3 }, [0]),
  (ArmFidelityLow.spec, { dim := 2, invRow := 0, lamN := 5, lamD := 1, fixedOther := some 0 }, [0]),
  (ArmFidelityMid.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, region := some (3/5), fixedOther := some 2 }, [0]),
  (ArmRefinement.spec, { dim := 2, invRow := 0, lamN := 5, lamD := 1, fixedOther := some 0 }, [0]),
  (AttitudeRate.spec, { dim := 6, invRow := 0, lamN := 2, lamD := 1, argIsRight := true, fixedOther := some 0 }, [0]),
  (EnduranceGainM1.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1 }, [0]),
  (EnduranceOrderlift1to2.spec, { dim := 3, invRow := 0, lamN := 2, lamD := 1 }, [0]),
  (EnduranceOrderlift2to3.spec, { dim := 4, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (MatchMultiEps.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 0 }, [0]),
  (MatchMultiRate.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 0, lamPerL := [(3,1),(2,1),(1,1)] }, [0]),
  (PlantFanHigh.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, region := some (3/5), fixedOther := some 3 }, [0]),
  (PlantFanLow.spec, { dim := 2, invRow := 0, lamN := 5, lamD := 1, fixedOther := some 0 }, [0]),
  (PlantFanMid.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, region := some (3/5), fixedOther := some 2 }, [0]),
  (RobotBraking.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 2 }, [0]),
  (Rover3tierM1.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 0 }, [0]),
  -- two components, per `pin_Rover3tierRung12Accel` and the spec's own `order`
  (Rover3tierRung12Accel.spec, { dim := 3, invRow := 0, lamN := 2, lamD := 1, argIsRight := true, fixedOther := some 0 }, [0, 1]),
  (Rover3tierRung12Coast.spec, { dim := 3, invRow := 1, lamN := 1, lamD := 1, argIsRight := true, fixedOther := some 1 }, [0]),
  (Rover4dBox.spec, { dim := 4, invRow := 0, lamN := 1, lamD := 1, fixedOther := some 1 }, [0]),
  (RoverAttitudeCone.spec, { dim := 12, invRow := 0, lamN := 17, lamD := 10, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1, 2, 3]),
  (RoverDofTerrainRung1.spec, { dim := 3, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (RoverDofTerrainRung2.spec, { dim := 6, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (RoverDofTerrainRung38d.spec, { dim := 8, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (RoverDofTerrainRung3.spec, { dim := 12, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (RoverDrag.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1 }, [0]),
  (RoverLadderRung1.spec, { dim := 3, invRow := 0, lamN := 1, lamD := 1 }, [0, 1]),
  (RoverLadderRung2.spec, { dim := 6, invRow := 0, lamN := 1, lamD := 1 }, [0, 2, 3, 1]),
  (RoverLadderRung3.spec, { dim := 8, invRow := 0, lamN := 9, lamD := 4, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1, 2, 3]),
  (RoverLadderRung4.spec, { dim := 12, invRow := 0, lamN := 17, lamD := 10, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1]),
  -- `VerdR6 l` runs left mode `l` against right mode `l`, not against a fixed 0, and
  -- carries eight invariant components plus the mode region `b6 m − s_R` at the tail.
  -- `pin_RoverRung2c` is what caught the earlier reading of this row, which rebuilt a
  -- single component at `(0, l)` — the wrong query for two of the three hypotheses.
  (RoverRung2c.spec, { dim := 6, invRow := 0, lamN := 1, lamD := 1,
                       tailCo := some 1, tailFlip := true,
                       tailKs := [0, 3/5, 7/5] }, [0, 1, 4, 5, 6, 7, 2, 3]),
  (RoverTerrainM1.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1 }, [0]),
  (RoverTierR1.spec, { dim := 3, invRow := 0, lamN := 19, lamD := 4, ceilCo := some 1, ceilFlip := true, ceilKs := [3/10] }, [0]),
  (Story1AttdistRungA.spec, { dim := 8, invRow := 1, lamN := 1, lamD := 1 }, [0, 1]),
  (Story1AttdistRungB.spec, { dim := 12, invRow := 0, lamN := 1, lamD := 1, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1]),
  (Story2LateralA.spec, { dim := 8, invRow := 0, lamN := 1, lamD := 1 }, [0, 1, 3, 4, 5, 6, 2]),
  (Story2LateralB.spec, { dim := 12, invRow := 0, lamN := 1, lamD := 1 }, [0, 1, 2, 4, 5, 6, 7, 3]),
  (Story3RolloverBase.spec, { dim := 12, invRow := 0, lamN := 5, lamD := 4, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1, 2, 3, 4]),
  (Story3RolloverRungA.spec, { dim := 12, invRow := 0, lamN := 27, lamD := 20, ceilCo := some 0, ceilFlip := false, ceilKs := [3/10, 1/2, 13/20] }, [0, 1, 2]),
  (Story3RolloverRungB.spec, { dim := 12, invRow := 1, lamN := 1, lamD := 1 }, [0, 1]),
  (Watertank.spec, { dim := 2, invRow := 0, lamN := 1, lamD := 1 }, [0])
]

/-- `--run-verdicts`' modal pass: every theorem's hypotheses, one route, no fallback. -/
def runModal (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== modal instances : {modalTable.length} verdict packs =="
      let mut ok := true
      for (spec, info, order) in modalTable do
        ok := (← runSpec s spec info order) && ok
      s.close
      if ok then IO.println "ALL MODAL HYPOTHESES DISCHARGED"
      else IO.println "MODAL PASS INCOMPLETE (see FAIL/SKIP above)"
      pure ok

end RelCertifier.Verdicts

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The suite_v2 modal verdict runner

Walks `packsV2` — one row per verdict pack an instance of `InstancesV2/Modal/` assumes
(benchmark, dimension, invariant row, strata order, λ, left and right mode) — rebuilds the
pack's queries from the emitted IR (`benchIRTableV2`) and the emitted extended cut
certificate (`cutTableV2`) through `modalVerdXQueries` (the builder `modalVerdX_of_queries`
proves denotes the instance's hypothesis), prints them with the tool's own `toScript`, and
reports Z3's verdict per component. Each instance's `Verd` is pinned to its row in
`VerdictsV2/PinsV2.lean`; the total is declared (`expectedModalV2`) and derived from the
table in `VerdictsV2/CoveragePinsV2.lean`. Anything it cannot rebuild is a SKIP and makes
the run non-green.
-/
import RelCertifier.VerdictsV2.ModalX
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.InstancesV2.Cuts
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage
import RelCertifier.Verdicts.RunHandoff
import RelCertifier.Verdicts.RunModal
import RelCertifier.Trusted.NonConnQuery
import RelCertifier.Trusted.JointVars
import RelCertifier.InstancesV2.BenchCovers

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- One verdict pack. -/
structure PackV2 where
  bench  : String
  dim    : ℕ
  invRow : ℕ := 0
  order  : List ℕ
  lamN   : ℕ := 1
  lamD   : ℕ := 1
  l      : ℕ
  m      : ℕ
  deriving Repr, Inhabited

def irV2 (b : String) : PProblem :=
  ((benchIRTableV2.find? (·.1 == b)).map (·.2)).getD default

def cutV2 (b : String) : EvolStrengtheningX :=
  ((cutTableV2.find? (·.1 == b)).map (·.2.2)).getD ⟨[], []⟩

def packLam (r : PackV2) : ℚ := (r.lamN : ℚ) / (r.lamD : ℚ)

/-- The pack's queries, as the runner builds them. -/
def packQueries (r : PackV2) : Option (List (List (IForm r.dim))) :=
  modalVerdXQueries (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order (packLam r) r.l r.m

/-- The hypothesis a pack row stands for (what the instances' `Verd`s are pinned to). -/
noncomputable def packVerd (r : PackV2) : Prop :=
  modalVerdX (irV2 r.bench) (cutV2 r.bench) r.dim r.invRow r.order ((packLam r : ℚ) : ℝ) r.l r.m

/-- The packs. Watertank: eleven (window, right mode) pairs, order `[0, 1]`. -/
def packsV2 : List PackV2 :=
  [ ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 0⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 2⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 0, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 1⟩, ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 2⟩,
    ⟨"watertank", 2, 0, [0, 1], 2, 1, 1, 3⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 0⟩, ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 1⟩,
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 2⟩, ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 3⟩,
    -- platoon_delay_profiles: two windows (rows 0, 1), right FOLLOW/GENTLE/ASSERTIVE, λ = 1
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"platoon_delay_profiles", 2, 0, [0, 1], 1, 1, 0, 2⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"platoon_delay_profiles", 2, 1, [0, 1], 1, 1, 1, 2⟩,
    -- acc_spoof_limp
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 0⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 1⟩,
    ⟨"acc_spoof_limp", 3, 0, [0, 1], 5, 4, 0, 2⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"acc_spoof_limp", 3, 1, [0, 1], 1, 1, 1, 2⟩,
    -- acc_tune_limp
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 0⟩,
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 1⟩,
    ⟨"acc_tune_limp", 3, 0, [0, 1], 3, 2, 0, 2⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"acc_tune_limp", 3, 1, [0, 1], 1, 1, 1, 2⟩,
    -- platoon_delay_linkloss
    ⟨"platoon_delay_linkloss", 3, 0, [0, 1], 1, 1, 0, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 0, [0, 1], 1, 1, 0, 1⟩,
    ⟨"platoon_delay_linkloss", 3, 1, [0, 1], 1, 1, 1, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 1, [0, 1], 1, 1, 1, 1⟩,
    ⟨"platoon_delay_linkloss", 3, 2, [0, 1], 1, 1, 2, 0⟩,
    ⟨"platoon_delay_linkloss", 3, 2, [0, 1], 1, 1, 2, 1⟩,
    -- quad_light_airframe_20
    ⟨"quad_light_airframe_20", 2, 0, [0, 1], 7, 4, 0, 0⟩,
    -- quad_light_profiles
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 0⟩,
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 1⟩,
    ⟨"quad_light_profiles", 2, 0, [0, 1], 5, 2, 0, 2⟩,
    -- quad_light_lag
    ⟨"quad_light_lag", 2, 0, [0], 7, 4, 0, 0⟩,
    -- charger_fast_setpoints
    ⟨"charger_fast_setpoints", 2, 0, [0], 1, 1, 0, 1⟩,
    ⟨"charger_fast_setpoints", 2, 0, [0], 1, 1, 0, 2⟩,
    ⟨"charger_fast_setpoints", 2, 1, [0], 1, 1, 1, 1⟩,
    ⟨"charger_fast_setpoints", 2, 1, [0], 1, 1, 1, 2⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 0⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 1⟩,
    ⟨"charger_fast_setpoints", 2, 2, [0], 1, 1, 2, 2⟩,
    -- acc_tune_lag
    ⟨"acc_tune_lag", 2, 0, [0], 5, 4, 0, 0⟩,
    -- acc_spoof_lag
    ⟨"acc_spoof_lag", 2, 0, [0], 5, 2, 0, 0⟩,
    -- charger_fast_tapers
    ⟨"charger_fast_tapers", 2, 0, [0], 1, 1, 0, 3⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 0⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 1⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 2⟩,
    ⟨"charger_fast_tapers", 2, 1, [0], 1, 1, 1, 3⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 0⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 1⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 2⟩,
    ⟨"charger_fast_tapers", 2, 2, [0], 1, 1, 2, 3⟩ ]

/-- Declared: the number of component queries the packs owe (one per component). -/
def expectedModalV2 : Nat := 97

/-- Run one pack. -/
def runPack (s : Z3Session) (r : PackV2) : IO Bool := do
  let p := irV2 r.bench
  let vars := p.L.stateVars
  let coord := fun (i : Fin r.dim) => vars.getD i.val s!"pad{i.val}"
  match packQueries r with
  | none =>
      IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m})  (rebuild failed)"
      pure false
  | some qss =>
      if qss.isEmpty then
        IO.println s!"  SKIP  {r.bench} (l={r.l},m={r.m})  (no component)"
        return false
      let mut ok := true
      for i in List.range qss.length do
        let qs := qss.getD i []
        let mut good := false
        let mut detail := ""
        for (rn, q) in [("A", qs.getD 0 IForm.tt), ("B", qs.getD 1 IForm.tt),
            ("C", qs.getD 2 IForm.tt)] do
          if good then pure () else
          match ← s.check (q.toScript coord) with
          | .ok .unsat => good := true; detail := detail ++ s!"{rn}=unsat"
          | .ok .sat => detail := detail ++ s!"{rn}=sat "
          | .ok v => detail := detail ++ s!"{rn}={reprStr v} "
          | .error e => detail := detail ++ s!"{rn}=err({e}) "
        if good then
          IO.println s!"  UNSAT ({detail})  {r.bench} (l={r.l},m={r.m}) comp={i}"
          RelCertifier.Verdicts.counted
        else
          IO.println s!"  FAIL  {r.bench} (l={r.l},m={r.m}) comp={i} : {detail}"
          ok := false
      pure ok

def runModalV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 modal instances : {packsV2.length} verdict packs =="
      let mut ok := true
      for r in packsV2 do
        ok := (← runPack s r) && ok
      s.close
      pure ok

/-! ## The handoff phase over suite_v2 -/

/-- Declared: one handoff query per declared left transition over the 45 suite_v2 files
(self-loops included; `CoveragePinsV2.derivedHandoffV2_eq` derives it from the IR table). -/
def expectedHandoffV2 : Nat := 186

/-- Declared handoff failures in suite_v2: none. -/
def expectedHandoffFailuresV2 : List (String × Nat × Nat) := []

def runHandoffAllV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 handoff : {benchIRTableV2.length} benchmarks =="
      let mut ok := true
      let mut fails : List (String × ℕ × ℕ) := []
      for (name, p) in benchIRTableV2 do
        let r ← RelCertifier.Verdicts.runHandoffBench s cfg name p (verbose := false)
        IO.println r.line
        if r.checked != r.declared then
          IO.eprintln s!"  [handoff] {name}: {r.checked} checked but {r.declared} declared"
          ok := false
        fails := fails ++ r.failing.map (fun f => (name, f.1.1, f.1.2))
      s.close
      let extra := fails.filter (fun f => !expectedHandoffFailuresV2.contains f)
      let stale := expectedHandoffFailuresV2.filter (fun f => !fails.contains f)
      if !extra.isEmpty then
        IO.eprintln s!"  [handoff] UNDECLARED failures: {extra}"; ok := false
      if !stale.isEmpty then
        IO.eprintln s!"  [handoff] stale declared failures: {stale}"; ok := false
      pure ok

/-! ## The non-connection phase over suite_v2 (the pruned edges of the emitted covers,
the source mode's cut rebuilt from the EXTENDED certificate, as the tool narrows it) -/

def prunedEdgesV2 : List (String × String × String) :=
  coverTableV2.flatMap (fun c => c.2.pruned.map (fun e => (c.1, e.1, e.2)))

/-- Declared: pruned edges in the suite_v2 covers, and two queries per edge. -/
def expectedPrunedEdgesV2 : Nat := 44
def expectedNonConnV2 : Nat := 88

def nonConnQueriesOfV2 (p : PProblem) (cX : EvolStrengtheningX) (src tgt : String) :
    Option ((n : ℕ) × (Fin n → String) × IForm n × IForm n) := do
  let vars := p.jointVars
  let n := vars.length
  let mR ← p.R.modes.find? (·.name == src)
  let mSuc ← p.R.modes.find? (·.name == tgt)
  let cutR ← RelCertifier.NonConn.cutOfAtoms vars n ((cutAtomsOfX cX.R src).map (·.atom))
  let (q1, q2) ← RelCertifier.NonConn.queries vars n cutR mR mSuc
  pure ⟨n, fun i => vars.getD i.val s!"pad{i.val}", q1, q2⟩

def runNonConnAllV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 non-connection : {prunedEdgesV2.length} pruned edge(s) =="
      let mut ok := true
      for (bench, src, tgt) in prunedEdgesV2 do
        match nonConnQueriesOfV2 (irV2 bench) (cutV2 bench) src tgt with
        | none =>
            IO.println s!"  FAIL  {bench} {src} -> {tgt}  (pruning queries did not rebuild)"
            ok := false
        | some ⟨_, coord, q1, q2⟩ =>
            for (tag, q) in [("source", q1), ("barrier", q2)] do
              match ← s.check (q.toScript coord) with
              | .ok .unsat =>
                  IO.println s!"  UNSAT [{tag}]  {bench} {src} -> {tgt}"
                  RelCertifier.Verdicts.counted
              | v =>
                  IO.println s!"  FAIL  {bench} {src} -> {tgt} [{tag}] → {reprStr (match v with | .ok r => reprStr r | .error e => e)}"
                  ok := false
      s.close
      pure ok

/-! ## The suite tally -/

/-- What a certification run over `benchmarks/suite_v2/*/input.txt` must produce, with
`RELCERT_IMPLIED_CUT=1`: all 45 certified. -/
structure ExpectedSuiteV2 where
  paths     : Nat := 45
  certified : Nat := 45
  declined  : Nat := 0
  errors    : Nat := 0
  deriving Repr

def expectedSuiteV2 : ExpectedSuiteV2 := {}

def checkSuiteV2 (nPaths certified declined errors : Nat) : IO Bool := do
  let e := expectedSuiteV2
  if nPaths != e.paths then
    IO.println s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
over {nPaths} path(s) — tally not enforced (the declared suite is {e.paths} paths)"
    return true
  else if certified == e.certified && declined == e.declined && errors == e.errors then
    IO.println s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
— matches the declared suite"
    return true
  else
    IO.eprintln s!"  [suite_v2] {certified} certified, {declined} declined, {errors} error(s) \
but the declared suite is {e.certified}/{e.declined}/{e.errors}"
    return false

/-! ## The 19 benchmarks copied from suite_uniform: their (legacy) modal packs

Their suite_v2 literal IS the legacy literal (`InstancesV2/SameIR.lean`, `rfl`), so the
legacy theorems and their verdict packs (pinned to `RunModal.modalTable` by
`Verdicts/ModalPinTable`) are about the suite_v2 files. This phase re-runs exactly those
rows of the legacy table, so `--run-verdicts-v2` alone discharges every hypothesis of the
suite_v2 battery. -/

def sameBenchV2 : List String :=
  ["match_multi_rate", "refinement_ladder_rover_rung1_2to3",
   "refinement_ladder_rover_rung2_3to6", "refinement_ladder_rover_rung2_6dof",
   "refinement_ladder_rover_rung2b_6dof", "refinement_ladder_rover_rung2c_6dof",
   "refinement_ladder_rover_rung3_6to8", "refinement_ladder_rover_rung4_8to12",
   "rover3tier_rung12", "rover_dof_terrain_rung1", "rover_dof_terrain_rung2",
   "rover_dof_terrain_rung3", "rover_dof_terrain_rung3_8d",
   "story1_attdist_rung_a_6to8", "story1_attdist_rung_b_12dof",
   "story2_lateral_rung_a_8dof", "story2_lateral_rung_b_12dof",
   "story3_rollover_base_12dof", "story3_rollover_ladder_rung_a"]

def sameModalTable : List (RelCertifier.ModalSpecs.VerdSpec × RelCertifier.Verdicts.RunInfo × List ℕ) :=
  RelCertifier.Verdicts.modalTable.filter (fun r => sameBenchV2.contains r.1.bench)

/-- Declared: the legacy modal queries of the 19 copied benchmarks
(`CoveragePinsV2.derivedSameModalV2_eq` derives it from `modalTable`). -/
def expectedSameModalV2 : Nat := 385

def runSameModalV2 (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== suite_v2 copied benchmarks : {sameModalTable.length} legacy verdict packs =="
      let mut ok := true
      for (spec, info, order) in sameModalTable do
        ok := (← RelCertifier.Verdicts.runSpec s spec info order) && ok
      s.close
      pure ok

end RelCertifier.VerdictsV2

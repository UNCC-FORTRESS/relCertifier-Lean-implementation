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
    ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 2⟩, ⟨"watertank", 2, 0, [0, 1], 1, 1, 2, 3⟩ ]

/-- Declared: the number of component queries the packs owe (one per component). -/
def expectedModalV2 : Nat := 22

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

end RelCertifier.VerdictsV2

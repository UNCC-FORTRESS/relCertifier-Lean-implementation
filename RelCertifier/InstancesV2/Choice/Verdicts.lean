/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Choice exhibits — verdict packs, pins, runner

One row per verdict pack the three choice exhibits assume (the diagonal pairings of the two
vehicle exhibits, six pairings of `watertank_choice`). Each instance's `Verd` is pinned to its
row by `rfl`-level unfolding (a wrong IR, certificate, λ, order or mode pair does not
compile); `modalVerdX_of_queries` (the rebuild denotes `modalVerdX`) closes the chain from the
printed query to the hypothesis. The runner rebuilds each row's queries with
`modalVerdXQueries`, prints them with `toScript`, and owes one `unsat` per component; the
total is declared (`expectedChoice`).
-/
import RelCertifier.VerdictsV2.ModalX
import RelCertifier.Trusted.Z3
import RelCertifier.Verdicts.Coverage
import RelCertifier.InstancesV2.Choice.Modal.VehicleHypercert
import RelCertifier.InstancesV2.Choice.Modal.VehicleAccelCopy
import RelCertifier.InstancesV2.Choice.Modal.WatertankChoice
import RelCertifier.InstancesV2.Modal.Watertank

namespace RelCertifier.ChoiceVerdicts

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- One verdict pack, carrying its IR and extended cut certificate directly. -/
structure PackC where
  bench  : String
  p      : PProblem
  c      : EvolStrengtheningX
  dim    : ℕ := 2
  invRow : ℕ
  order  : List ℕ := [0, 1]
  lamN   : ℕ := 1
  lamD   : ℕ := 1
  l      : ℕ
  m      : ℕ

instance : Inhabited PackC := ⟨⟨"", default, ⟨[], []⟩, 2, 0, [], 1, 1, 0, 0⟩⟩

def packLam (r : PackC) : ℚ := (r.lamN : ℚ) / (r.lamD : ℚ)

def packQueries (r : PackC) : Option (List (List (IForm r.dim))) :=
  modalVerdXQueries r.p r.c r.dim r.invRow r.order (packLam r) r.l r.m

noncomputable def packVerd (r : PackC) : Prop :=
  modalVerdX r.p r.c r.dim r.invRow r.order ((packLam r : ℚ) : ℝ) r.l r.m

def hyp (l : ℕ) : PackC :=
  { bench := "vehicle_hypercert", p := vehicle_hypercert_IRv2, c := vehicle_hypercert_cutsV2X,
    invRow := l, l := l, m := l }
def acc (l : ℕ) : PackC :=
  { bench := "vehicle_accel_copy", p := vehicle_accel_copy_IRc, c := vehicle_accel_copy_cutsCX,
    invRow := l, l := l, m := l }
/-- The suite's `watertank`, the pairing its emitted `Low` cover reaches that the suite runner
does not carry (`Low/High` at 2): consumed by the general-theorem instance. -/
def wt (l m lamN lamD : ℕ) : PackC :=
  { bench := "watertank", p := watertank_IRv2, c := watertank_cutsV2X,
    invRow := 0, lamN := lamN, lamD := lamD, l := l, m := m }
def wtc (l m lamN lamD : ℕ) : PackC :=
  { bench := "watertank_choice", p := watertank_choice_IRc, c := watertank_choice_cutsCX,
    invRow := 0, lamN := lamN, lamD := lamD, l := l, m := m }

/-- The packs: the emitted covers' pairings the instances consume (λ and order as emitted;
`watertank_choice` `Low/High` at 1 is consumed by the general-theorem instance). -/
def packsC : List PackC :=
  [hyp 0, hyp 1, hyp 2, hyp 3, hyp 4,
   acc 0, acc 1, acc 2,
   wtc 0 0 2 1, wtc 0 1 7 2, wtc 0 2 1 1, wtc 0 3 1 1, wtc 1 2 1 1, wtc 1 3 1 1, wtc 2 3 1 1,
   wt 0 3 2 1]

/-- Two components per pack (the invariant row has two). -/
def expectedChoice : Nat := 32

/-! ## Pins -/

theorem pin_hyp (l : ℕ) : ChoiceVehicleHypercert.Verd l = packVerd (hyp l) := by
  simp [ChoiceVehicleHypercert.Verd, packVerd, hyp, packLam, ChoiceVehicleHypercert.lam]

theorem pin_acc (l : ℕ) : ChoiceVehicleAccelCopy.Verd l = packVerd (acc l) := by
  simp [ChoiceVehicleAccelCopy.Verd, packVerd, acc, packLam, ChoiceVehicleAccelCopy.lam]

theorem pin_wtc_00 : ChoiceWatertank.Verd 0 0 = packVerd (wtc 0 0 2 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wtc_01 : ChoiceWatertank.Verd 0 1 = packVerd (wtc 0 1 7 2) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wtc_02 : ChoiceWatertank.Verd 0 2 = packVerd (wtc 0 2 1 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wtc_03 : ChoiceWatertank.Verd 0 3 = packVerd (wtc 0 3 1 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wt_03 : V2Watertank.Verd 0 3 = packVerd (wt 0 3 2 1) := by
  simp [V2Watertank.Verd, packVerd, wt, packLam, V2Watertank.lam]
theorem pin_wtc_12 : ChoiceWatertank.Verd 1 2 = packVerd (wtc 1 2 1 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wtc_13 : ChoiceWatertank.Verd 1 3 = packVerd (wtc 1 3 1 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]
theorem pin_wtc_23 : ChoiceWatertank.Verd 2 3 = packVerd (wtc 2 3 1 1) := by
  simp [ChoiceWatertank.Verd, packVerd, wtc, packLam, ChoiceWatertank.lam]

/-- Each pack's hypothesis from Z3 `unsat` verdicts on its rebuilt queries. -/
theorem packVerd_of_queries (r : PackC) {qss : List (List (IForm r.dim))}
    (hq : packQueries r = some qss)
    (hz3 : ∀ i (hi : i < qss.length), ∃ q ∈ qss[i], z3solve q.toHost = Verdict.unsat) :
    packVerd r := by
  unfold packVerd
  have := modalVerdX_of_queries hq hz3
  simpa [packLam] using this

/-! ## Runner -/

def runPack (s : Z3Session) (r : PackC) : IO Bool := do
  let vars := r.p.L.stateVars
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

def runChoice (cfg : Z3Config) : IO Bool := do
  match ← Z3Session.start cfg with
  | .error e => IO.eprintln s!"ERROR: z3: {e}"; return false
  | .ok s =>
      IO.println s!"== choice exhibits : {packsC.length} verdict packs =="
      let mut ok := true
      for r in packsC do
        ok := (← runPack s r) && ok
      s.close
      let n ← RelCertifier.Verdicts.dischargedCount.get
      let full ← RelCertifier.Verdicts.checkPhase "choice" n expectedChoice
      pure (ok && full)

end RelCertifier.ChoiceVerdicts

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Pinning the runner's *code*, not just its data

`ModalPinTable` and `ModalTablePins` tie the runner's `RunInfo` row to the theorems.
That left one link read rather than proved: the code turning those fields into the query
actually handed to the printer. Three short stretches of it:

* `modalLamI` — the pair `(lamN, lamD)` becomes the rational `lamN/lamD`. No data pin
  said that pair *means* that number, so changing the `/` to a `*` would have left every
  pin compiling while Z3 was asked about a different λ. That is the dangerous direction:
  a larger λ is a *weaker* flow condition, so the query would likely still come back
  `unsat` and the run would stay green.
* `modalHeadI` — `ceilCo`/`ceilFlip`/`ceilKs` become the head term `R_c − k_m`.
* `modalRoutes` — the three queries tried per component are routes A, B and C.

Each theorem states that one of those constructions, at the arguments the pins fix,
denotes the host-level term the hypothesis names. They are the functions `runSpec` and
`checkComp` call, not copies, so these constrain the runner itself.

`List.getD` does not reduce at a variable index, so the per-window λ rows and the
per-mode heads are stated at each asserted index rather than generically.

With this file the chain is kernel-checked from a theorem's `Verd…` down to the IR
query handed to `toScript`. What remains outside the kernel is the printer and Z3 —
the frozen trust base.
-/
import RelCertifier.Verdicts.ModalPinTable

namespace RelCertifier.Verdicts

open RelCertifier RelCertifier.Parse DL

set_option autoImplicit false

/-! ## The three routes

Generic in every argument: whatever component, fields and domain the runner reaches
`checkComp` with, the queries formed are exactly the three the hypotheses disjoin. -/

theorem modalRoutes_toHost {n : ℕ} (g : ITerm n) (fL fR : Fin n → ITerm n)
    (lam : ITerm n) (dom : IForm n) :
    (modalRoutes g fL fR lam dom).map (fun r => r.2.toHost)
      = [flowQuery ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
           lam.toHost, dom.toHost⟩,
         flowQueryStrict ⟨g.toHost, (fun i => (fL i).toHost), (fun i => (fR i).toHost),
           lam.toHost, dom.toHost⟩,
         flowQuerySuperlevel ⟨g.toHost, (fun i => (fL i).toHost),
           (fun i => (fR i).toHost), lam.toHost, dom.toHost⟩] := by
  simp [modalRoutes, iflowQuery_toHost, iflowQueryStrict_toHost,
    iflowQuerySuperlevel_toHost]

/-! ## λ — one theorem per row -/

theorem lam_ArmChainRung3 (l : ℕ) :
    (modalLamI (row 0).2.1 l 2).toHost = Term.const (1 : ℝ) := by
  have hp : (row 0).2.1.lamPerL = [] := rfl
  have hn : (row 0).2.1.lamN = 1 := rfl
  have hd : (row 0).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_ArmFidelityMid (l : ℕ) :
    (modalLamI (row 1).2.1 l 2).toHost = Term.const (1 : ℝ) := by
  have hp : (row 1).2.1.lamPerL = [] := rfl
  have hn : (row 1).2.1.lamN = 1 := rfl
  have hd : (row 1).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_AttitudeRate (l : ℕ) :
    (modalLamI (row 2).2.1 l 6).toHost = Term.const (2 : ℝ) := by
  have hp : (row 2).2.1.lamPerL = [] := rfl
  have hn : (row 2).2.1.lamN = 2 := rfl
  have hd : (row 2).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_EnduranceGainM1 (l : ℕ) :
    (modalLamI (row 3).2.1 l 2).toHost = Term.const (1 : ℝ) := by
  have hp : (row 3).2.1.lamPerL = [] := rfl
  have hn : (row 3).2.1.lamN = 1 := rfl
  have hd : (row 3).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_EnduranceOrderlift1to2 (l : ℕ) :
    (modalLamI (row 4).2.1 l 3).toHost = Term.const (2 : ℝ) := by
  have hp : (row 4).2.1.lamPerL = [] := rfl
  have hn : (row 4).2.1.lamN = 2 := rfl
  have hd : (row 4).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_EnduranceOrderlift2to3 (l : ℕ) :
    (modalLamI (row 5).2.1 l 4).toHost = Term.const (1 : ℝ) := by
  have hp : (row 5).2.1.lamPerL = [] := rfl
  have hn : (row 5).2.1.lamN = 1 := rfl
  have hd : (row 5).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Rover3tierRung12Accel (l : ℕ) :
    (modalLamI (row 7).2.1 l 3).toHost = Term.const (2 : ℝ) := by
  have hp : (row 7).2.1.lamPerL = [] := rfl
  have hn : (row 7).2.1.lamN = 2 := rfl
  have hd : (row 7).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Rover3tierRung12Coast (l : ℕ) :
    (modalLamI (row 8).2.1 l 3).toHost = Term.const (1 : ℝ) := by
  have hp : (row 8).2.1.lamPerL = [] := rfl
  have hn : (row 8).2.1.lamN = 1 := rfl
  have hd : (row 8).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Rover4dBox (l : ℕ) :
    (modalLamI (row 9).2.1 l 4).toHost = Term.const (1 : ℝ) := by
  have hp : (row 9).2.1.lamPerL = [] := rfl
  have hn : (row 9).2.1.lamN = 1 := rfl
  have hd : (row 9).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverAttitudeCone (l : ℕ) :
    (modalLamI (row 10).2.1 l 12).toHost = Term.const ((17 : ℝ) / 10) := by
  have hp : (row 10).2.1.lamPerL = [] := rfl
  have hn : (row 10).2.1.lamN = 17 := rfl
  have hd : (row 10).2.1.lamD = 10 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverDofTerrainRung1 (l : ℕ) :
    (modalLamI (row 11).2.1 l 3).toHost = Term.const (1 : ℝ) := by
  have hp : (row 11).2.1.lamPerL = [] := rfl
  have hn : (row 11).2.1.lamN = 1 := rfl
  have hd : (row 11).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverDofTerrainRung2 (l : ℕ) :
    (modalLamI (row 12).2.1 l 6).toHost = Term.const (1 : ℝ) := by
  have hp : (row 12).2.1.lamPerL = [] := rfl
  have hn : (row 12).2.1.lamN = 1 := rfl
  have hd : (row 12).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverDofTerrainRung38d (l : ℕ) :
    (modalLamI (row 13).2.1 l 8).toHost = Term.const (1 : ℝ) := by
  have hp : (row 13).2.1.lamPerL = [] := rfl
  have hn : (row 13).2.1.lamN = 1 := rfl
  have hd : (row 13).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverDofTerrainRung3 (l : ℕ) :
    (modalLamI (row 14).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 14).2.1.lamPerL = [] := rfl
  have hn : (row 14).2.1.lamN = 1 := rfl
  have hd : (row 14).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverDrag (l : ℕ) :
    (modalLamI (row 15).2.1 l 2).toHost = Term.const (1 : ℝ) := by
  have hp : (row 15).2.1.lamPerL = [] := rfl
  have hn : (row 15).2.1.lamN = 1 := rfl
  have hd : (row 15).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverLadderRung1 (l : ℕ) :
    (modalLamI (row 16).2.1 l 3).toHost = Term.const (1 : ℝ) := by
  have hp : (row 16).2.1.lamPerL = [] := rfl
  have hn : (row 16).2.1.lamN = 1 := rfl
  have hd : (row 16).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverLadderRung2 (l : ℕ) :
    (modalLamI (row 17).2.1 l 6).toHost = Term.const (1 : ℝ) := by
  have hp : (row 17).2.1.lamPerL = [] := rfl
  have hn : (row 17).2.1.lamN = 1 := rfl
  have hd : (row 17).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverLadderRung3 (l : ℕ) :
    (modalLamI (row 18).2.1 l 8).toHost = Term.const ((9 : ℝ) / 4) := by
  have hp : (row 18).2.1.lamPerL = [] := rfl
  have hn : (row 18).2.1.lamN = 9 := rfl
  have hd : (row 18).2.1.lamD = 4 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverLadderRung4 (l : ℕ) :
    (modalLamI (row 19).2.1 l 12).toHost = Term.const ((17 : ℝ) / 10) := by
  have hp : (row 19).2.1.lamPerL = [] := rfl
  have hn : (row 19).2.1.lamN = 17 := rfl
  have hd : (row 19).2.1.lamD = 10 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverRung2c (l : ℕ) :
    (modalLamI (row 20).2.1 l 6).toHost = Term.const (1 : ℝ) := by
  have hp : (row 20).2.1.lamPerL = [] := rfl
  have hn : (row 20).2.1.lamN = 1 := rfl
  have hd : (row 20).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverTerrainM1 (l : ℕ) :
    (modalLamI (row 21).2.1 l 2).toHost = Term.const (1 : ℝ) := by
  have hp : (row 21).2.1.lamPerL = [] := rfl
  have hn : (row 21).2.1.lamN = 1 := rfl
  have hd : (row 21).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_RoverTierR1 (l : ℕ) :
    (modalLamI (row 22).2.1 l 3).toHost = Term.const ((19 : ℝ) / 4) := by
  have hp : (row 22).2.1.lamPerL = [] := rfl
  have hn : (row 22).2.1.lamN = 19 := rfl
  have hd : (row 22).2.1.lamD = 4 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story1AttdistRungA (l : ℕ) :
    (modalLamI (row 23).2.1 l 8).toHost = Term.const (1 : ℝ) := by
  have hp : (row 23).2.1.lamPerL = [] := rfl
  have hn : (row 23).2.1.lamN = 1 := rfl
  have hd : (row 23).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story1AttdistRungB (l : ℕ) :
    (modalLamI (row 24).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 24).2.1.lamPerL = [] := rfl
  have hn : (row 24).2.1.lamN = 1 := rfl
  have hd : (row 24).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story2LateralA (l : ℕ) :
    (modalLamI (row 25).2.1 l 8).toHost = Term.const (1 : ℝ) := by
  have hp : (row 25).2.1.lamPerL = [] := rfl
  have hn : (row 25).2.1.lamN = 1 := rfl
  have hd : (row 25).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story2LateralB (l : ℕ) :
    (modalLamI (row 26).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 26).2.1.lamPerL = [] := rfl
  have hn : (row 26).2.1.lamN = 1 := rfl
  have hd : (row 26).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story3RolloverBase (l : ℕ) :
    (modalLamI (row 27).2.1 l 12).toHost = Term.const ((5 : ℝ) / 4) := by
  have hp : (row 27).2.1.lamPerL = [] := rfl
  have hn : (row 27).2.1.lamN = 5 := rfl
  have hd : (row 27).2.1.lamD = 4 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story3RolloverRungA (l : ℕ) :
    (modalLamI (row 28).2.1 l 12).toHost = Term.const ((27 : ℝ) / 20) := by
  have hp : (row 28).2.1.lamPerL = [] := rfl
  have hn : (row 28).2.1.lamN = 27 := rfl
  have hd : (row 28).2.1.lamD = 20 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story3RolloverRungB (l : ℕ) :
    (modalLamI (row 29).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 29).2.1.lamPerL = [] := rfl
  have hn : (row 29).2.1.lamN = 1 := rfl
  have hd : (row 29).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

/-! ### Per-window λ — at each asserted left index -/

open RelCertifier.MatchMultiRateModal in
theorem lam_MatchMultiRate_0 :
    (modalLamI (row 6).2.1 0 2).toHost = Term.const (lamM 0 : ℝ) := by
  have hp : (row 6).2.1.lamPerL = [(3,1),(2,1),(1,1)] := rfl
  have hn : (row 6).2.1.lamN = 1 := rfl
  have hd : (row 6).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd, lamM] <;> norm_num

open RelCertifier.MatchMultiRateModal in
theorem lam_MatchMultiRate_1 :
    (modalLamI (row 6).2.1 1 2).toHost = Term.const (lamM 1 : ℝ) := by
  have hp : (row 6).2.1.lamPerL = [(3,1),(2,1),(1,1)] := rfl
  have hn : (row 6).2.1.lamN = 1 := rfl
  have hd : (row 6).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd, lamM] <;> norm_num

open RelCertifier.MatchMultiRateModal in
theorem lam_MatchMultiRate_2 :
    (modalLamI (row 6).2.1 2 2).toHost = Term.const (lamM 2 : ℝ) := by
  have hp : (row 6).2.1.lamPerL = [(3,1),(2,1),(1,1)] := rfl
  have hn : (row 6).2.1.lamN = 1 := rfl
  have hd : (row 6).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd, lamM] <;> norm_num

/-! ## Ceiling heads — per row, at each right mode -/

open RelCertifier.RoverAttitudeConeModal in
theorem head_ceilC_21_0 (h : 0 < 12) :
    (modalHeadI (row 10).2.1.ceilCo (row 10).2.1.ceilFlip (row 10).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilC 0] := by
  have hc : (row 10).2.1.ceilCo = some 0 := rfl
  have hf : (row 10).2.1.ceilFlip = false := rfl
  have hk : (row 10).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilC, hc, hf, hk] <;> norm_num

open RelCertifier.RoverAttitudeConeModal in
theorem head_ceilC_21_1 (h : 0 < 12) :
    (modalHeadI (row 10).2.1.ceilCo (row 10).2.1.ceilFlip (row 10).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilC 1] := by
  have hc : (row 10).2.1.ceilCo = some 0 := rfl
  have hf : (row 10).2.1.ceilFlip = false := rfl
  have hk : (row 10).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilC, hc, hf, hk] <;> norm_num

open RelCertifier.RoverAttitudeConeModal in
theorem head_ceilC_21_2 (h : 0 < 12) :
    (modalHeadI (row 10).2.1.ceilCo (row 10).2.1.ceilFlip (row 10).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilC 2] := by
  have hc : (row 10).2.1.ceilCo = some 0 := rfl
  have hf : (row 10).2.1.ceilFlip = false := rfl
  have hk : (row 10).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilC, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung3Modal in
theorem head_ceilR_29_0 (h : 0 < 8) :
    (modalHeadI (row 18).2.1.ceilCo (row 18).2.1.ceilFlip (row 18).2.1.ceilKs 0
      (n := 8) h).map ITerm.toHost = [ceilR 0] := by
  have hc : (row 18).2.1.ceilCo = some 0 := rfl
  have hf : (row 18).2.1.ceilFlip = false := rfl
  have hk : (row 18).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilR, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung3Modal in
theorem head_ceilR_29_1 (h : 0 < 8) :
    (modalHeadI (row 18).2.1.ceilCo (row 18).2.1.ceilFlip (row 18).2.1.ceilKs 1
      (n := 8) h).map ITerm.toHost = [ceilR 1] := by
  have hc : (row 18).2.1.ceilCo = some 0 := rfl
  have hf : (row 18).2.1.ceilFlip = false := rfl
  have hk : (row 18).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilR, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung3Modal in
theorem head_ceilR_29_2 (h : 0 < 8) :
    (modalHeadI (row 18).2.1.ceilCo (row 18).2.1.ceilFlip (row 18).2.1.ceilKs 2
      (n := 8) h).map ITerm.toHost = [ceilR 2] := by
  have hc : (row 18).2.1.ceilCo = some 0 := rfl
  have hf : (row 18).2.1.ceilFlip = false := rfl
  have hk : (row 18).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilR, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung4Modal in
theorem head_ceilF_30_0 (h : 0 < 12) :
    (modalHeadI (row 19).2.1.ceilCo (row 19).2.1.ceilFlip (row 19).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilF 0] := by
  have hc : (row 19).2.1.ceilCo = some 0 := rfl
  have hf : (row 19).2.1.ceilFlip = false := rfl
  have hk : (row 19).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung4Modal in
theorem head_ceilF_30_1 (h : 0 < 12) :
    (modalHeadI (row 19).2.1.ceilCo (row 19).2.1.ceilFlip (row 19).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilF 1] := by
  have hc : (row 19).2.1.ceilCo = some 0 := rfl
  have hf : (row 19).2.1.ceilFlip = false := rfl
  have hk : (row 19).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.RoverLadderRung4Modal in
theorem head_ceilF_30_2 (h : 0 < 12) :
    (modalHeadI (row 19).2.1.ceilCo (row 19).2.1.ceilFlip (row 19).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilF 2] := by
  have hc : (row 19).2.1.ceilCo = some 0 := rfl
  have hf : (row 19).2.1.ceilFlip = false := rfl
  have hk : (row 19).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.RoverTierR1Modal in
theorem head_ceilX_33_0 (h : 0 < 3) :
    (modalHeadI (row 22).2.1.ceilCo (row 22).2.1.ceilFlip (row 22).2.1.ceilKs 0
      (n := 3) h).map ITerm.toHost = [ceilX 0] := by
  have hc : (row 22).2.1.ceilCo = some 1 := rfl
  have hf : (row 22).2.1.ceilFlip = true := rfl
  have hk : (row 22).2.1.ceilKs = [3/10] := rfl
  simp [modalHeadI, ITerm.toHost, ceilX, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_35_0 (h : 0 < 12) :
    (modalHeadI (row 24).2.1.ceilCo (row 24).2.1.ceilFlip (row 24).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilF 0] := by
  have hc : (row 24).2.1.ceilCo = some 0 := rfl
  have hf : (row 24).2.1.ceilFlip = false := rfl
  have hk : (row 24).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_35_1 (h : 0 < 12) :
    (modalHeadI (row 24).2.1.ceilCo (row 24).2.1.ceilFlip (row 24).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilF 1] := by
  have hc : (row 24).2.1.ceilCo = some 0 := rfl
  have hf : (row 24).2.1.ceilFlip = false := rfl
  have hk : (row 24).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_35_2 (h : 0 < 12) :
    (modalHeadI (row 24).2.1.ceilCo (row 24).2.1.ceilFlip (row 24).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilF 2] := by
  have hc : (row 24).2.1.ceilCo = some 0 := rfl
  have hf : (row 24).2.1.ceilFlip = false := rfl
  have hk : (row 24).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverBaseModal in
theorem head_ceilB_38_0 (h : 0 < 12) :
    (modalHeadI (row 27).2.1.ceilCo (row 27).2.1.ceilFlip (row 27).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilB 0] := by
  have hc : (row 27).2.1.ceilCo = some 0 := rfl
  have hf : (row 27).2.1.ceilFlip = false := rfl
  have hk : (row 27).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilB, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverBaseModal in
theorem head_ceilB_38_1 (h : 0 < 12) :
    (modalHeadI (row 27).2.1.ceilCo (row 27).2.1.ceilFlip (row 27).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilB 1] := by
  have hc : (row 27).2.1.ceilCo = some 0 := rfl
  have hf : (row 27).2.1.ceilFlip = false := rfl
  have hk : (row 27).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilB, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverBaseModal in
theorem head_ceilB_38_2 (h : 0 < 12) :
    (modalHeadI (row 27).2.1.ceilCo (row 27).2.1.ceilFlip (row 27).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilB 2] := by
  have hc : (row 27).2.1.ceilCo = some 0 := rfl
  have hf : (row 27).2.1.ceilFlip = false := rfl
  have hk : (row 27).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilB, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverRungAModal in
theorem head_ceilA_39_0 (h : 0 < 12) :
    (modalHeadI (row 28).2.1.ceilCo (row 28).2.1.ceilFlip (row 28).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilA 0] := by
  have hc : (row 28).2.1.ceilCo = some 0 := rfl
  have hf : (row 28).2.1.ceilFlip = false := rfl
  have hk : (row 28).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilA, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverRungAModal in
theorem head_ceilA_39_1 (h : 0 < 12) :
    (modalHeadI (row 28).2.1.ceilCo (row 28).2.1.ceilFlip (row 28).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilA 1] := by
  have hc : (row 28).2.1.ceilCo = some 0 := rfl
  have hf : (row 28).2.1.ceilFlip = false := rfl
  have hk : (row 28).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilA, hc, hf, hk] <;> norm_num

open RelCertifier.Story3RolloverRungAModal in
theorem head_ceilA_39_2 (h : 0 < 12) :
    (modalHeadI (row 28).2.1.ceilCo (row 28).2.1.ceilFlip (row 28).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilA 2] := by
  have hc : (row 28).2.1.ceilCo = some 0 := rfl
  have hf : (row 28).2.1.ceilFlip = false := rfl
  have hk : (row 28).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilA, hc, hf, hk] <;> norm_num

/-! ## The tail face — `rover_rung2c`, at each asserted mode -/

open RelCertifier.RoverRung2cModal in
theorem head_tail_31_0 (h : 0 < 6) :
    (modalHeadI (row 20).2.1.tailCo (row 20).2.1.tailFlip (row 20).2.1.tailKs 0
      (n := 6) h).map ITerm.toHost = [lowFace (b6 0) (Rv 1)] := by
  have hc : (row 20).2.1.tailCo = some 1 := rfl
  have hf : (row 20).2.1.tailFlip = true := rfl
  have hk : (row 20).2.1.tailKs = [0, 3/5, 7/5] := rfl
  simp [modalHeadI, ITerm.toHost, lowFace, b6, hc, hf, hk] <;> norm_num

open RelCertifier.RoverRung2cModal in
theorem head_tail_31_1 (h : 0 < 6) :
    (modalHeadI (row 20).2.1.tailCo (row 20).2.1.tailFlip (row 20).2.1.tailKs 1
      (n := 6) h).map ITerm.toHost = [lowFace (b6 1) (Rv 1)] := by
  have hc : (row 20).2.1.tailCo = some 1 := rfl
  have hf : (row 20).2.1.tailFlip = true := rfl
  have hk : (row 20).2.1.tailKs = [0, 3/5, 7/5] := rfl
  simp [modalHeadI, ITerm.toHost, lowFace, b6, hc, hf, hk] <;> norm_num

open RelCertifier.RoverRung2cModal in
theorem head_tail_31_2 (h : 0 < 6) :
    (modalHeadI (row 20).2.1.tailCo (row 20).2.1.tailFlip (row 20).2.1.tailKs 2
      (n := 6) h).map ITerm.toHost = [lowFace (b6 2) (Rv 1)] := by
  have hc : (row 20).2.1.tailCo = some 1 := rfl
  have hf : (row 20).2.1.tailFlip = true := rfl
  have hk : (row 20).2.1.tailKs = [0, 3/5, 7/5] := rfl
  simp [modalHeadI, ITerm.toHost, lowFace, b6, hc, hf, hk] <;> norm_num

/-! ## The mode-keyed instances' rows (`Instances/*Handoff.lean`) -/

theorem lam_Story1AttdistRungASteep (l : ℕ) :
    (modalLamI (row 30).2.1 l 8).toHost = Term.const (1 : ℝ) := by
  have hp : (row 30).2.1.lamPerL = [] := rfl
  have hn : (row 30).2.1.lamN = 1 := rfl
  have hd : (row 30).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story3RolloverRungBSteep (l : ℕ) :
    (modalLamI (row 31).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 31).2.1.lamPerL = [] := rfl
  have hn : (row 31).2.1.lamN = 1 := rfl
  have hd : (row 31).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story1AttdistRungBRow0 (l : ℕ) :
    (modalLamI (row 32).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 32).2.1.lamPerL = [] := rfl
  have hn : (row 32).2.1.lamN = 1 := rfl
  have hd : (row 32).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story1AttdistRungBRow1 (l : ℕ) :
    (modalLamI (row 33).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 33).2.1.lamPerL = [] := rfl
  have hn : (row 33).2.1.lamN = 1 := rfl
  have hd : (row 33).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

theorem lam_Story1AttdistRungBRow2 (l : ℕ) :
    (modalLamI (row 34).2.1 l 12).toHost = Term.const (1 : ℝ) := by
  have hp : (row 34).2.1.lamPerL = [] := rfl
  have hn : (row 34).2.1.lamN = 1 := rfl
  have hd : (row 34).2.1.lamD = 1 := rfl
  simp [modalLamI, ITerm.toHost, hp, hn, hd] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_44_0 (h : 0 < 12) :
    (modalHeadI (row 32).2.1.ceilCo (row 32).2.1.ceilFlip (row 32).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilF 0] := by
  have hc : (row 32).2.1.ceilCo = some 0 := rfl
  have hf : (row 32).2.1.ceilFlip = false := rfl
  have hk : (row 32).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_44_1 (h : 0 < 12) :
    (modalHeadI (row 32).2.1.ceilCo (row 32).2.1.ceilFlip (row 32).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilF 1] := by
  have hc : (row 32).2.1.ceilCo = some 0 := rfl
  have hf : (row 32).2.1.ceilFlip = false := rfl
  have hk : (row 32).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_44_2 (h : 0 < 12) :
    (modalHeadI (row 32).2.1.ceilCo (row 32).2.1.ceilFlip (row 32).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilF 2] := by
  have hc : (row 32).2.1.ceilCo = some 0 := rfl
  have hf : (row 32).2.1.ceilFlip = false := rfl
  have hk : (row 32).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_45_0 (h : 0 < 12) :
    (modalHeadI (row 33).2.1.ceilCo (row 33).2.1.ceilFlip (row 33).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilF 0] := by
  have hc : (row 33).2.1.ceilCo = some 0 := rfl
  have hf : (row 33).2.1.ceilFlip = false := rfl
  have hk : (row 33).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_45_1 (h : 0 < 12) :
    (modalHeadI (row 33).2.1.ceilCo (row 33).2.1.ceilFlip (row 33).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilF 1] := by
  have hc : (row 33).2.1.ceilCo = some 0 := rfl
  have hf : (row 33).2.1.ceilFlip = false := rfl
  have hk : (row 33).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_45_2 (h : 0 < 12) :
    (modalHeadI (row 33).2.1.ceilCo (row 33).2.1.ceilFlip (row 33).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilF 2] := by
  have hc : (row 33).2.1.ceilCo = some 0 := rfl
  have hf : (row 33).2.1.ceilFlip = false := rfl
  have hk : (row 33).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_46_0 (h : 0 < 12) :
    (modalHeadI (row 34).2.1.ceilCo (row 34).2.1.ceilFlip (row 34).2.1.ceilKs 0
      (n := 12) h).map ITerm.toHost = [ceilF 0] := by
  have hc : (row 34).2.1.ceilCo = some 0 := rfl
  have hf : (row 34).2.1.ceilFlip = false := rfl
  have hk : (row 34).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_46_1 (h : 0 < 12) :
    (modalHeadI (row 34).2.1.ceilCo (row 34).2.1.ceilFlip (row 34).2.1.ceilKs 1
      (n := 12) h).map ITerm.toHost = [ceilF 1] := by
  have hc : (row 34).2.1.ceilCo = some 0 := rfl
  have hf : (row 34).2.1.ceilFlip = false := rfl
  have hk : (row 34).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

open RelCertifier.Story1AttdistRungBModal in
theorem head_ceilF_46_2 (h : 0 < 12) :
    (modalHeadI (row 34).2.1.ceilCo (row 34).2.1.ceilFlip (row 34).2.1.ceilKs 2
      (n := 12) h).map ITerm.toHost = [ceilF 2] := by
  have hc : (row 34).2.1.ceilCo = some 0 := rfl
  have hf : (row 34).2.1.ceilFlip = false := rfl
  have hk : (row 34).2.1.ceilKs = [3/10, 1/2, 13/20] := rfl
  simp [modalHeadI, ITerm.toHost, ceilF, hc, hf, hk] <;> norm_num

end RelCertifier.Verdicts

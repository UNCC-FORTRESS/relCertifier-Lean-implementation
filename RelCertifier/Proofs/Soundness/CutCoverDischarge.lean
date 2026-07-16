/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# S2 dischargers — `CoverCertMC` fields from the emitted cut certificates

Per-benchmark instances feed `CoverCertMC` from three ingredient kinds:

* **`hiff`** — `hostAtom_iff`: the lowered atom formula ≡ its safe-side term `≤ 0`,
  fully generic (the failure branches of the two lowerings align, so the `getD`
  defaults `⊤`/`0` keep the equivalence);
* **O1 entry** — `hostGuard_cutAtoms_sat`: the mode guard's lowering implies each cut
  atom's lowering, given the guard's lowering succeeds (a per-benchmark `simp`+`decide`
  kernel fact) — atom membership in `cutAtoms` is kernel-decided (`evolStrengtheningWF`);
* **staying** — the route adapters from `CutLift` (`atom_boxle_{L,R}_{strict,nonstrict}`,
  `AtomFact.ofLie`), plus `atomsStay_L_frozen_dyn` here: LEFT atoms along the
  frozen-left dynamic-reposition flows are constant (every field is `0` where the atom
  reads), a Lean fact needing no Z3.
-/
import RelCertifier.Proofs.Soundness.CutCover
import RelCertifier.Proofs.Encoding.CoverInstance

namespace RelCertifier
open DL Parse Set RelCertifier.Oracle

variable {n : ℕ}

/-! ## Host-level atom data (`getD`-wrapped, like `hostGuard`/`hostEvolve`) -/

/-- The lowered atom formula. -/
noncomputable def hostAtomF (vars : List String) (n : ℕ) (side : Side) (a : PForm) :
    Formula (Var n) :=
  ((Run.lowerF vars n side a).map IForm.toHost).getD Formula.tt

/-- The lowered atom's safe-side term. -/
noncomputable def hostAtomG (vars : List String) (n : ℕ) (side : Side) (a : PForm) :
    Term (Var n) :=
  ((cutAtomG vars n side a).map ITerm.toHost).getD (Term.const 0)

/-! ## `hiff` -/

/-- The lowered atom formula is satisfaction-equivalent to `hostAtomG ≤ 0`, with the
lowering-failure branches aligned (`⊤` ↔ `0 ≤ 0`). -/
theorem hostAtom_iff {vars : List String} {side : Side} {op : String} {x y : PExpr}
    (hop : op = "<=" ∨ op = ">=") (ν : DL.State (Var n)) :
    Formula.sat (hostAtomF vars n side (.cmp op x y)) ν
      ↔ Term.eval (hostAtomG vars n side (.cmp op x y)) ν ≤ 0 := by
  unfold hostAtomF hostAtomG
  rcases hex : Run.lowerE vars n side x with _ | ex
  · have hf : Run.lowerF vars n side (.cmp op x y) = none := by
      simp [Run.lowerF, hex]
    have hg : cutAtomG vars n side (.cmp op x y) = (none : Option (ITerm n)) := by
      rcases hop with rfl | rfl <;> simp [cutAtomG, hex]
    rw [hf, hg]
    simp [Formula.sat, Term.eval]
  · rcases hey : Run.lowerE vars n side y with _ | ey
    · have hf : Run.lowerF vars n side (.cmp op x y) = none := by
        simp [Run.lowerF, hex, hey]
      have hg : cutAtomG vars n side (.cmp op x y) = (none : Option (ITerm n)) := by
        rcases hop with rfl | rfl <;> simp [cutAtomG, hex, hey]
      rw [hf, hg]
      simp [Formula.sat, Term.eval]
    · rcases hop with rfl | rfl
      · have hf : Run.lowerF vars n side (.cmp "<=" x y)
            = some (IForm.cmp CompOp.le ex ey) := by
          simp [Run.lowerF, hex, hey]
        have hg : cutAtomG vars n side (.cmp "<=" x y)
            = some (ITerm.bin .sub ex ey) := by
          simp [cutAtomG, hex, hey]
        rw [hf, hg]
        simpa using cutAtomG_sat (Or.inl rfl) hf hg ν
      · have hf : Run.lowerF vars n side (.cmp ">=" x y)
            = some (IForm.cmp CompOp.ge ex ey) := by
          simp [Run.lowerF, hex, hey]
        have hg : cutAtomG vars n side (.cmp ">=" x y)
            = some (ITerm.bin .sub ey ex) := by
          simp [cutAtomG, hex, hey]
        rw [hf, hg]
        simpa using cutAtomG_sat (Or.inr rfl) hf hg ν

/-! ## O1 -/

/-- A cut atom of a successfully-lowered formula lowers too. -/
theorem lowerF_cutAtom_isSome {vars : List String} {side : Side} {f a : PForm}
    (ha : a ∈ cutAtoms f) :
    ∀ {fI : IForm n}, Run.lowerF vars n side f = some fI →
      ∃ aI : IForm n, Run.lowerF vars n side a = some aI := by
  induction f with
  | and p q ihp ihq =>
      intro fI hf
      unfold Run.lowerF at hf
      rcases hp : Run.lowerF vars n side p with _ | pI <;> rw [hp] at hf
      · simp at hf
      rcases hq : Run.lowerF vars n side q with _ | qI <;> rw [hq] at hf
      · simp at hf
      unfold cutAtoms at ha
      rcases List.mem_append.mp ha with h | h
      · exact ihp h hp
      · exact ihq h hq
  | cmp op x y =>
      intro fI hf
      unfold cutAtoms at ha
      split at ha
      · rw [List.mem_singleton.mp ha]
        exact ⟨fI, hf⟩
      · exact absurd ha (by simp)
  | tt => intro fI hf; exact absurd ha (by simp [cutAtoms])
  | or p q ihp ihq => intro fI hf; exact absurd ha (by simp [cutAtoms])
  | not p ihp => intro fI hf; exact absurd ha (by simp [cutAtoms])

/-- **O1, `getD`-level.** Wherever the mode guard's lowering holds, each of its cut
atoms' lowerings holds — given the guard lowers (per-benchmark kernel fact). -/
theorem hostGuard_cutAtoms_sat {vars : List String} {side : Side} {m : PMode}
    {a : PForm} (ha : a ∈ cutAtoms m.guard)
    (hsome : (Run.lowerF vars n side m.guard : Option (IForm n)).isSome = true) :
    ∀ ν : DL.State (Var n), Formula.sat (hostGuard vars n side m) ν →
      Formula.sat (hostAtomF vars n side a) ν := by
  intro ν hν
  obtain ⟨fI, hf⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨aI, haI⟩ := lowerF_cutAtom_isSome ha hf
  unfold hostGuard at hν
  rw [hf] at hν
  unfold hostAtomF
  rw [haI]
  exact cutAtoms_sat ha hf haI ν (by simpa using hν)

/-! ## Left atoms are frozen along the dynamic-reposition flows -/

/-- The Lie derivative with both fields zeroed evaluates to `0`. -/
theorem eval_lieDeriv_zero (g : Term (Var n)) (x : DL.State (Var n)) :
    Term.eval (lieDeriv g (fun _ => Term.const 0) (fun _ => Term.const 0)
      (Term.const 1)) x = 0 := by
  unfold lieDeriv
  induction (List.finRange n) with
  | nil => simp [sumTerm, Term.eval]
  
  | cons i l ih => simp [sumTerm, Term.eval, AOp.interp, ih]

/-- **Left atoms stay along the frozen-left dynamic flows** — every field is `0` where
the atom reads (`Lv`-only, and the left block of `dynSys` is the zero field), so the
atom is constant. No Z3. -/
theorem atomsStay_L_frozen_dyn (fR : Fin n → Term (Var n)) (dom : Formula (Var n))
    (atoms : List (CutAtomP n))
    (hfv : ∀ a ∈ atoms, ∀ i : Fin n, Rv i ∉ a.2.fv) :
    AtomsStay atoms (jointSys (fun _ => Term.const 0) fR (Term.const 1)) dom := by
  intro a ha ν hb
  refine atom_boxle_L_nonstrict a.2 (fun _ => Term.const 0) fR (Term.const 1) dom
    Formula.tt (hfv a ha) (fun x _ => by simp [Formula.sat]) ?_ hb
  intro σ hσ
  obtain ⟨-, hgt⟩ := hσ
  rw [show Formula.sat (Formula.cmp .gt (lieDeriv a.2 (fun _ => Term.const 0)
      (fun _ => Term.const 0) (Term.const 1)) (Term.const 0)) σ ↔
    Term.eval (lieDeriv a.2 (fun _ => Term.const 0) (fun _ => Term.const 0)
      (Term.const 1)) σ > 0 from by simp [Formula.sat, CompOp.interp, Term.eval]] at hgt
  rw [eval_lieDeriv_zero] at hgt
  exact lt_irrefl 0 hgt

end RelCertifier

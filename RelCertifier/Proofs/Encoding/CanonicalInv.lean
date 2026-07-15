/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# R3 — the canonical relational invariant (docs/ROADMAP.md R3)

The `hψ`/`hinvL`/`hinvR` residuals were per-benchmark hypotheses: SOME relational formula
`ϕinv` with `encode ϕinv = invLe g` and side-split projections. This file constructs it
once, generically, for ANY lowered invariant term:

`rsplit` projects every variable occurrence on its own side — `Lv` reads become `⌊·⌋_L`,
`Rv` reads `⌊·⌋_R` — and `RTerm.enc` erases projections homomorphically, so the encoding
identity is definitional-by-induction. No lhs/rhs convention is needed: mixed-side terms
(e.g. rover_drag's `R_vx − L_vx ≤ 0.05`) split per occurrence. The projection bounds
(`varsL ⊆ Lv`, `varsR ⊆ Rv`) follow from the invariant's Aux-freeness, which the lowering
provides premise-free (`invToG_fv_LR`).
-/
import RelCertifier.Proofs.Encoding.UniformFvDischarge

namespace RelCertifier
open DL DLRel Set

variable {n : ℕ}

/-- Side-split reification: every variable occurrence projected on its own side
(`Aux` falls to the left projection — harmless, excluded by Aux-freeness). -/
def rsplit : Term (Var n) → RTerm (Var n)
  | .var v =>
      match v.1 with
      | Side.R => RTerm.proj DLRel.Side.R (.var v)
      | _ => RTerm.proj DLRel.Side.L (.var v)
  | .const c => RTerm.proj DLRel.Side.L (.const c)
  | .binop op a b => RTerm.binop op (rsplit a) (rsplit b)

/-- The canonical relational invariant: `⌊g⌋ ≤ 0`, per-occurrence side-projected. -/
def canonInv (g : Term (Var n)) : RFormula (Var n) :=
  RFormula.cmp CompOp.le (rsplit g) (RTerm.proj DLRel.Side.L (Term.const 0))

/-! ## The encoding identity -/

theorem rsplit_renameR_refl (t : Term (Var n)) :
    (rsplit t).renameR (Equiv.refl (Var n)) = rsplit t := by
  induction t with
  | var v =>
      unfold rsplit
      match hv : v.1 with
      | Side.R => simp [RTerm.renameR]
      | Side.L => simp [RTerm.renameR]
      | Side.Aux => simp [RTerm.renameR]
  | const c => simp [rsplit, RTerm.renameR]
  | binop op a b iha ihb => simp [rsplit, RTerm.renameR, iha, ihb]

theorem rsplit_enc (t : Term (Var n)) : (rsplit t).enc = t := by
  induction t with
  | var v =>
      unfold rsplit
      match v.1 with
      | Side.R => rfl
      | Side.L => rfl
      | Side.Aux => rfl
  | const c => rfl
  | binop op a b iha ihb => simp [rsplit, RTerm.enc, iha, ihb]

/-- **The encoding identity, generic** — discharges every `hψ` residual. -/
theorem encode_canonInv (g : Term (Var n)) :
    encode (Equiv.refl (Var n)) (canonInv g) = invLe g := by
  unfold encode canonInv invLe
  simp only [RFormula.renameR, RTerm.renameR, Term.rename_refl, rsplit_renameR_refl]
  simp only [RFormula.enc, RTerm.enc, rsplit_enc]

/-! ## The projection bounds -/

theorem rsplit_varsL_sub (t : Term (Var n)) :
    (rsplit t).varsL ⊆ {x ∈ t.fv | x.1 ≠ Side.R} := by
  induction t with
  | var v =>
      unfold rsplit
      match hv : v.1 with
      | Side.R => simp [RTerm.varsL]
      | Side.L =>
          intro x hx
          simp only [RTerm.varsL, Term.fv, Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨by simp [Term.fv], by simp [hv]⟩
      | Side.Aux =>
          intro x hx
          simp only [RTerm.varsL, Term.fv, Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨by simp [Term.fv], by simp [hv]⟩
  | const c =>
      intro x hx
      simp [rsplit, RTerm.varsL, Term.fv] at hx
  | binop op a b iha ihb =>
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨hfv, hside⟩ := iha hx
        exact ⟨Or.inl hfv, hside⟩
      · obtain ⟨hfv, hside⟩ := ihb hx
        exact ⟨Or.inr hfv, hside⟩

theorem rsplit_varsR_sub (t : Term (Var n)) :
    (rsplit t).varsR ⊆ {x ∈ t.fv | x.1 = Side.R} := by
  induction t with
  | var v =>
      unfold rsplit
      match hv : v.1 with
      | Side.R =>
          intro x hx
          simp only [RTerm.varsR, Term.fv, Set.mem_singleton_iff] at hx
          subst hx
          exact ⟨by simp [Term.fv], hv⟩
      | Side.L => simp [RTerm.varsR]
      | Side.Aux => simp [RTerm.varsR]
  | const c =>
      intro x hx
      simp [rsplit, RTerm.varsR] at hx
  | binop op a b iha ihb =>
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨hfv, hside⟩ := iha hx
        exact ⟨Or.inl hfv, hside⟩
      · obtain ⟨hfv, hside⟩ := ihb hx
        exact ⟨Or.inr hfv, hside⟩

/-- **Left projection bound** — discharges every `hinvL` residual (Aux-freeness via
`hgLR`, itself premise-free from the lowering). -/
theorem canonInv_varsL (g : Term (Var n)) (hgLR : g.fv ⊆ range Lv ∪ range Rv) :
    (canonInv g).varsL ⊆ range Lv := by
  intro x hx
  simp only [canonInv, RFormula.varsL] at hx
  rcases hx with hx | hx
  · obtain ⟨hfv, hside⟩ := rsplit_varsL_sub g hx
    rcases hgLR hfv with h | ⟨i, rfl⟩
    · exact h
    · exact absurd rfl hside
  · simp only [RTerm.varsL, Term.fv] at hx
    exact absurd hx (by simp)

/-- **Right projection bound** — discharges every `hinvR` residual. -/
theorem canonInv_varsR (g : Term (Var n)) :
    (canonInv g).varsR ⊆ range Rv := by
  intro x hx
  simp only [canonInv, RFormula.varsR] at hx
  rcases hx with hx | hx
  · obtain ⟨-, hside⟩ := rsplit_varsR_sub g hx
    exact ⟨x.2, Prod.ext hside.symm rfl⟩
  · simp only [RTerm.varsR] at hx
    exact absurd hx (by simp)

end RelCertifier

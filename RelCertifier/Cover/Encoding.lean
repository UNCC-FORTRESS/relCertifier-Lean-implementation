/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

Stage 3 (5) — the global ∀∃ encoding bridge.

The cover's verdict is the paper's `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`, a relational (bi-state)
formula. dL-rel `RFormula.encoding_correct(_exists)` bridges bi-state truth to host dL
truth, so a Z3 UNSAT on the encoded negation certifies the bi-state validity of the
global claim. This is the old dL-relcertifier bridge in its correct home: the ∀∃
fragment is exactly what dL-rel's `faShape` / `encode` were built for.

`theorem3_encoded` here proves `rvalid` of the **flat** `theorem3Form L R ϕ_inv` (right side
`R*` the flat choice-star) via one Z3 UNSAT — a valid but weaker over-approximation. The
**transition-faithful** landing (right side `R_real`, declared transitions only) is the
independent `BridgeFinish.theorem3_faithful`; both routes rest on the same `z3_unsat_sound` leaf.

Trust boundary unchanged: the only assumed fact is Z3 UNSAT (`z3_unsat_sound`); the
bridge itself is a proven theorem of dL-rel.
-/
import RelCertifier.Cover
import DLRel

namespace RelCertifier

open DL DLRel

variable {V : Type*}

/-- **Encoding bridge** (= the old `certify_sound`, in its Stage-3 home). If the host
encoding of `¬P` is unsatisfiable (a trusted Z3 UNSAT) and the freshness side-condition
holds, then the relational formula `P` is valid at every bi-state (`rvalid P`).

Cites dL-rel `RFormula.encoding_correct_exists`: bi-state truth of `¬P` would exhibit a
satisfying host state of `encode ρ (¬P)`, contradicting UNSAT. -/
theorem rvalid_of_encoded_unsat (ρ : V ≃ V) (P : RFormula V)
    (hd : Disjoint (RFormula.neg P).varsL (ρ '' (RFormula.neg P).varsR))
    (hunsat : ∀ σ, ¬ Formula.sat (encode ρ (RFormula.neg P)) σ) :
    RFormula.rvalid P := by
  intro bs
  by_contra hbs
  -- `¬ sat P bs` is definitionally `sat (¬P) bs`
  have hneg : RFormula.sat (RFormula.neg P) bs := hbs
  obtain ⟨σ, _, hsat⟩ :=
    (RFormula.encoding_correct_exists ρ (RFormula.neg P) hd bs).mp hneg
  exact hunsat σ hsat

/-- The paper's **Theorem 3** relational formula: `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`, i.e.
`ϕ_inv → ⟨⟨ the ∀∃ modality over the left/right star programs ⟩⟩ ϕ_inv`, as a dL-rel
`RFormula` (via `faShape`, the encoded `[|(α,?⊤)|]⟨⟨(?⊤,β)⟩⟩`). -/
def theorem3Form (L R : Program V) (ϕinv : RFormula V) : RFormula V :=
  RFormula.imp ϕinv (faShape (Program.star L) (Program.star R) ϕinv)

/-- **Theorem 3, encoded and certified.** A trusted Z3 UNSAT on the host encoding of
`¬(ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv)` certifies the global ∀∃ relational invariant at every
bi-state. This packages the cover's conclusion into dL via `encoding_correct`. -/
theorem theorem3_encoded (ρ : V ≃ V) (L R : Program V) (ϕinv : RFormula V)
    (hd : Disjoint (RFormula.neg (theorem3Form L R ϕinv)).varsL
            (ρ '' (RFormula.neg (theorem3Form L R ϕinv)).varsR))
    (hunsat : ∀ σ, ¬ Formula.sat (encode ρ (RFormula.neg (theorem3Form L R ϕinv))) σ) :
    RFormula.rvalid (theorem3Form L R ϕinv) :=
  rvalid_of_encoded_unsat ρ (theorem3Form L R ϕinv) hd hunsat

end RelCertifier

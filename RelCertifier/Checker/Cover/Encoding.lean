/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The ∀∃ encoding bridge

The conclusion of Theorem 3 (Soundness of Synthesis) is a relational formula of the shape
of Definition 1 and Eq. (10), `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`. dL-rel's
`RFormula.encoding_correct(_exists)` relates bi-state truth to host dL truth, so a Z3 UNSAT
on the encoded negation of such a formula gives its bi-state validity. The ∀∃ fragment is the
one dL-rel's `faShape` / `encode` are built for.

`theorem3_encoded` proves `rvalid` of `theorem3Form L R ϕ_inv`, whose right side is the flat
choice-star `R*`, from one Z3 UNSAT. The form whose right side takes declared transitions only
is `BridgeFinish.theorem3_faithful`; both rest on the same `z3_unsat_sound` axiom.

The only assumed fact is the Z3 UNSAT (`z3_unsat_sound`); the bridge itself is a theorem of
dL-rel.
-/
import RelCertifier.Checker.Cover
import DLRel

namespace RelCertifier

open DL DLRel

variable {V : Type*}

/-- **Encoding bridge.** If the host
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

/-- The relational formula of Definition 1 and Eq. (10): `ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`, i.e.
`ϕ_inv → ⟨⟨ the ∀∃ modality over the left/right star programs ⟩⟩ ϕ_inv`, as a dL-rel
`RFormula` (via `faShape`, the encoded `[|(α,?⊤)|]⟨⟨(?⊤,β)⟩⟩`). -/
def theorem3Form (L R : Program V) (ϕinv : RFormula V) : RFormula V :=
  RFormula.imp ϕinv (faShape (Program.star L) (Program.star R) ϕinv)

/-- **The ∀∃ invariance formula from one UNSAT.** A trusted Z3 UNSAT on the host encoding of
`¬(ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv)` gives the ∀∃ relational invariance of Definition 1 at every
bi-state, through `rvalid_of_encoded_unsat`. -/
theorem theorem3_encoded (ρ : V ≃ V) (L R : Program V) (ϕinv : RFormula V)
    (hd : Disjoint (RFormula.neg (theorem3Form L R ϕinv)).varsL
            (ρ '' (RFormula.neg (theorem3Form L R ϕinv)).varsR))
    (hunsat : ∀ σ, ¬ Formula.sat (encode ρ (RFormula.neg (theorem3Form L R ϕinv))) σ) :
    RFormula.rvalid (theorem3Form L R ϕinv) :=
  rvalid_of_encoded_unsat ρ (theorem3Form L R ϕinv) hd hunsat

end RelCertifier

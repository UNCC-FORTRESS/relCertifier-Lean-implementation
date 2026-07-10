/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Step (3) — CSF `faModal` ⟹ the NFM'25 ∀∃ relational modality `[|(L,R)⟩⟩ϕ`

The last arrow of the main chain, built from two **proven** theorems:
* `DLRel.sat_encode_faShape` : `encode ρ (faShape α β ψ) ≡ faModal ρ α β (encode ρ ψ)` — the
  dL-caltiming ∀∃-modality *is* the host encoding of the dL-rel ∀∃ relational modality
  `faShape α β ψ = [|(α,?⊤)|]⟨⟨(?⊤,β)⟩⟩ψ = [|(α,β)⟩⟩ψ`. **Same renaming `ρ`.**
* `DLRel.RFormula.encoding_correct` (Theorem 2) : bi-state truth of a rel formula ≡ host truth
  of its encoding at a bridged join state.

Composing: a CSF `faModal ρ L* R* (encode ρ ϕ)` at the join state `σ` gives the **bi-state**
∀∃ relational invariant `[|(L*,R*)⟩⟩ϕ`. This is the paper's Theorem-3 conclusion, on the
mechanized relational logic — not a bespoke object.
-/
import RelCertifier.CSFBridge
import DLRel

namespace RelCertifier

open DL DLCalTiming DLRel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`faModal` ⟹ `[|(L,R)⟩⟩ϕ`.** If the CSF ∀∃-modality `faModal ρ α β (encode ρ ψ)` holds at
a join state `σ` bridging the bi-state `bs`, then the NFM'25 ∀∃ relational modality
`faShape α β ψ` (`= [|(α,β)⟩⟩ψ`) holds at `bs`. Pure composition of the two proven bridges. -/
theorem faModal_to_faShape (ρ : V ≃ V) (α β : Program V) (ψ : RFormula V)
    (σ : State V) (bs : BiState V)
    (hd : Disjoint (faShape α β ψ).varsL (ρ '' (faShape α β ψ).varsR))
    (hb : Bridges ρ (faShape α β ψ).varsL (faShape α β ψ).varsR bs σ)
    (h : Formula.sat (faModal ρ α β (encode ρ ψ)) σ) :
    RFormula.sat (faShape α β ψ) bs := by
  rw [RFormula.encoding_correct ρ (faShape α β ψ) hd bs σ hb, sat_encode_faShape]
  exact h

end RelCertifier

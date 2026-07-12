/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Reification — assemble the mode-list into choice-star programs, apply the proven rules

NOTE (flat vs transition-faithful). `reified_relational` closes the loop with BOTH sides as flat
choice-stars; the right `(⨆ modes)*` is a weaker over-approximation of the declared automaton. The
transition-faithful right side (`R_real`, jumps only along declared edges) is assembled instead in
`BridgeUnit1-3`/`BridgeFinish` (`theorem3_faithful`), reusing `faModal_bigChoiceL`/`faModal_LOCK`.

The final CSF-side assembly of the single-sync (B=1) chain. Builds `leftBody`/`rightBody` as the
nondeterministic **choice** over the parsed modes (`bigChoice`), discharges the per-iteration
lockstep step `hstep` from the per-pair `faModal`s (via `faModal_unionL`/`faModal_unionR`), and
concludes the looped relational modality via `relational_loop` (⟵ `faModal_LOCK`).

Fidelity (see the session gate):
* **No new trusted surface.** This is proving-through-proven-rules over the mode-list; lowering
  `PProblem → mode-list` (dynamics, domains from `evolve`, invariant) is the existing parser.
* **Flat over-approximation.** `leftBody* = (⨆ modes)*` admits *any* mode sequence, so the `box`
  `[L*]` claim is **stronger** than the benchmark's transition-restricted automaton — it *implies*
  the paper's real-automaton `[|(L*,R*)⟩⟩ϕ`. Sound; stated as the over-approximation, not the
  exact automaton.
* **Single-sync scope.** One right match per left mode (`faModal_unionR`'s one-fixed-branch is
  exactly single-sync). B>1 needs `faModal_MULTI` + the clock — out of scope here.
* **Domain = evolution domain.** The per-pair `faModal`s come from `segment_faModal`, whose cert
  is on `domL∧domR` = the evolve fields (guard-bug class barred).
-/
import RelCertifier.EncodingBridge

namespace RelCertifier

open DL DLCalTiming DLRel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nondeterministic choice over a list of programs. Empty ↦ `?false` (no successful run);
each `cons` is a `choice` (the trailing `?false` branch is dead — harmless). -/
def bigChoice : List (Program V) → Program V
  | []      => Program.test (Formula.neg Formula.tt)
  | p :: ps => Program.choice p (bigChoice ps)

/-- **Right choice fold.** A `faModal` for one right branch `Qm ∈ Qs` lifts to the whole choice
`bigChoice Qs` (single-sync: the one fixed matching branch). ⟵ `faModal_unionR`. -/
theorem faModal_bigChoiceR (ρ : V ≃ V) (P : Program V) (φ : Formula V) (ω : State V)
    (Qm : Program V) (h : Formula.sat (faModal ρ P Qm φ) ω) :
    ∀ (Qs : List (Program V)), Qm ∈ Qs → Formula.sat (faModal ρ P (bigChoice Qs) φ) ω
  | [], hm => absurd hm (by simp)
  | q :: qs, hm => by
      rw [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact faModal_unionR ρ P Qm (bigChoice qs) φ ω (Or.inl h)
      · exact faModal_unionR ρ P q (bigChoice qs) φ ω
          (Or.inr (faModal_bigChoiceR ρ P φ ω Qm h qs hm))

/-- **Left choice fold.** If `faModal` holds for every left branch, it holds for the whole choice
`bigChoice Ps` (∀ left mode). ⟵ `faModal_unionL`. -/
theorem faModal_bigChoiceL (ρ : V ≃ V) (Q : Program V) (φ : Formula V) (ω : State V) :
    ∀ (Ps : List (Program V)), (∀ P ∈ Ps, Formula.sat (faModal ρ P Q φ) ω) →
      Formula.sat (faModal ρ (bigChoice Ps) Q φ) ω := by
  intro Ps
  induction Ps with
  | nil =>
      -- `bigChoice [] = ?false`; `[?false]⟨…⟩` is vacuously true (no successful left run)
      intro _
      rw [faModal_sat]; intro ν hν
      simp [bigChoice, Program.sem, Formula.sat] at hν
  | cons p ps ih =>
      intro h
      show Formula.sat (faModal ρ (Program.choice p (bigChoice ps)) Q φ) ω
      refine faModal_unionL ρ p (bigChoice ps) Q φ ω ⟨h p (List.mem_cons_self ..), ?_⟩
      exact ih (fun P hP => h P (List.mem_cons_of_mem p hP))

/-- **Reified looped relational guarantee (the assembly).** Given the left/right mode programs
(`leftProgs`/`rightProgs`), a single-sync **pairing** (`hpair`: each left mode has one matching
right mode in `rightProgs` whose per-pair `faModal` preserves the invariant `ψ` from any
invariant-satisfying state — discharged by `segment_relational`'s underlying `segment_faModal`),
left/right variable disjointness (`hd`), the initial invariant, and `Bridges`, the NFM'25 ∀∃
relational modality over the **looped choice-automata** `[|((⨆leftProgs)*, (⨆rightProgs)*)⟩⟩ ψ`
holds at the bi-state.

Assembles the per-pair `faModal`s into the loop step via `faModal_bigChoiceL` (∀ left mode) +
`faModal_bigChoiceR` (pick the single-sync match), then applies `relational_loop` (⟵
`faModal_LOCK`). `ρ = id`. `(⨆leftProgs)*` is the flat over-approximation of the real left
automaton (any mode sequence) — the `box` claim is thus **stronger** than, and implies, the
paper's transition-restricted `[|(L*,R*)⟩⟩ϕ`. Proving-through-proven-rules; no new trusted
surface (lowering `PProblem → mode-list` is the existing parser). -/
theorem reified_relational {n : ℕ}
    (leftProgs rightProgs : List (Program (Var n)))
    (ψ : RFormula (Var n)) (ν : State (Var n)) (bs : BiState (Var n))
    (hpair : ∀ P ∈ leftProgs, ∃ Qm ∈ rightProgs, ∀ σ,
        Formula.sat (encode (Equiv.refl (Var n)) ψ) σ →
        Formula.sat (faModal (Equiv.refl (Var n)) P Qm (encode (Equiv.refl (Var n)) ψ)) σ)
    (hd : Disjoint (Program.vars (bigChoice leftProgs))
        (Program.vars ((bigChoice rightProgs).rename (Equiv.refl (Var n)))))
    (hinv : Formula.sat (encode (Equiv.refl (Var n)) ψ) ν)
    (hdd : Disjoint (faShape (Program.star (bigChoice leftProgs))
          (Program.star (bigChoice rightProgs)) ψ).varsL
        (Equiv.refl (Var n) '' (faShape (Program.star (bigChoice leftProgs))
          (Program.star (bigChoice rightProgs)) ψ).varsR))
    (hb : Bridges (Equiv.refl (Var n))
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (bigChoice rightProgs)) ψ).varsL
        (faShape (Program.star (bigChoice leftProgs))
          (Program.star (bigChoice rightProgs)) ψ).varsR bs ν) :
    RFormula.sat (faShape (Program.star (bigChoice leftProgs))
      (Program.star (bigChoice rightProgs)) ψ) bs := by
  refine relational_loop (bigChoice leftProgs) (bigChoice rightProgs) ψ ν bs hd hinv ?_ hdd hb
  intro σ hσ
  refine faModal_bigChoiceL (Equiv.refl (Var n)) (bigChoice rightProgs)
    (encode (Equiv.refl (Var n)) ψ) σ leftProgs ?_
  intro P hP
  obtain ⟨Qm, hQm, hpp⟩ := hpair P hP
  exact faModal_bigChoiceR (Equiv.refl (Var n)) P (encode (Equiv.refl (Var n)) ψ) σ
    Qm (hpp σ hσ) rightProgs hQm

end RelCertifier

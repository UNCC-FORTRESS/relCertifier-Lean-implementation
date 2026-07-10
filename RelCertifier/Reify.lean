/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Reification, base case — a cover segment ⟹ a CSF ∀∃ modality (`faModal`)

Step (2) of the main soundness chain, base case. A single certified cover segment
(`flow_cert_sound`: `g≤0` preserved by the joint flow on the evolution domain) becomes one
CSF ∀∃-ODE guarantee `faModal id (ode leftBlock domL) (ode rightBlock domR) (g≤0)`, via the
domain-restricted base rule `faModal_ODE_G'`.

Two design facts (see the session scoping):
* **`ρ = Equiv.refl`.** `jointSys = leftBlock ++ rightBlock` already binds disjoint
  `Side.L`/`Side.R` variables, so the NFM'25 separating renaming is the identity here —
  `sysY.rename id = sysY`, `jointSys = sysX ++ sysY` directly. No Side-swap mirror.
* **`hdisj` needs dynamics independence.** `ode_combine` (inside `faModal_ODE_G'`) needs the
  left/right read-vars disjoint — i.e. `fL` reads only `Side.L`, `λ·fR` only `Side.R`. The
  refinement/fidelity suite satisfies this (separate models, coupled only through `λ` and the
  invariant). Taken as an explicit hypothesis `hdisj`; a shared-state candidate would fail it
  (a checkable, parser-level `hdisj`-gate, not needed for the suite).

`hExist'` (the in-domain right witness) is the remaining dischargeable hypothesis — supplied by
the cover's joint-domain co-execution (its right projection stays in `domR`); wired in the
successor/assembly step.
-/
import RelCertifier.CSFBridge
import RelCertifier.FlowCert

namespace RelCertifier

open DL Set DLCalTiming

variable {n : ℕ}

/-- Left block of `jointSys`: `Lᵢ' = fL i`. -/
def leftBlock (fL : Fin n → Term (Var n)) : ODESystem (Var n) :=
  (List.finRange n).map (fun i => (Lv i, fL i))

/-- Right block of `jointSys`: `Rᵢ' = λ·fR i`. -/
def rightBlock (fR : Fin n → Term (Var n)) (lam : Term (Var n)) : ODESystem (Var n) :=
  (List.finRange n).map (fun i => (Rv i, Term.binop .mul lam (fR i)))

/-- `jointSys` is literally the two blocks concatenated (definitional). -/
theorem jointSys_split (fL fR : Fin n → Term (Var n)) (lam : Term (Var n)) :
    jointSys fL fR lam = leftBlock fL ++ rightBlock fR lam := rfl

/-- Renaming a term by the identity equivalence is the identity. -/
@[simp] theorem Term.rename_refl (t : Term (Var n)) :
    t.rename (Equiv.refl (Var n)) = t := by
  induction t with
  | var x => rfl
  | const c => rfl
  | binop op a b iha ihb => simp only [Term.rename, iha, ihb]

/-- Renaming an ODE system by the identity equivalence is the identity. -/
@[simp] theorem ODESystem.rename_refl (sys : ODESystem (Var n)) :
    sys.rename (Equiv.refl (Var n)) = sys := by
  unfold ODESystem.rename
  conv_rhs => rw [← List.map_id sys]
  refine List.map_congr_left ?_
  intro p _
  simp only [Equiv.refl_apply, Term.rename_refl, id_eq, Prod.mk.eta]

-- Renaming a program / formula by the identity equivalence is the identity (mutual).
mutual
@[simp] theorem Program.rename_refl : ∀ (α : Program (Var n)),
    α.rename (Equiv.refl (Var n)) = α
  | .assign x θ => by simp only [Program.rename, Equiv.refl_apply, Term.rename_refl]
  | .assignAny x => by simp only [Program.rename, Equiv.refl_apply]
  | .ode sys ψ => by
      simp only [Program.rename, ODESystem.rename_refl, Formula.rename_refl]
  | .test φ => by simp only [Program.rename, Formula.rename_refl]
  | .seq a b => by simp only [Program.rename, Program.rename_refl a, Program.rename_refl b]
  | .choice a b => by simp only [Program.rename, Program.rename_refl a, Program.rename_refl b]
  | .star a => by simp only [Program.rename, Program.rename_refl a]
@[simp] theorem Formula.rename_refl : ∀ (φ : Formula (Var n)),
    φ.rename (Equiv.refl (Var n)) = φ
  | .tt => rfl
  | .cmp op a b => by simp only [Formula.rename, Term.rename_refl]
  | .neg φ => by simp only [Formula.rename, Formula.rename_refl φ]
  | .and a b => by simp only [Formula.rename, Formula.rename_refl a, Formula.rename_refl b]
  | .all x φ => by simp only [Formula.rename, Equiv.refl_apply, Formula.rename_refl φ]
  | .box α φ => by simp only [Formula.rename, Program.rename_refl α, Formula.rename_refl φ]
end

/-- The invariant `g ≤ 0` as a `Formula`; `sat` unfolds to the `BoxLe` scalar condition. -/
def invLe (g : Term (Var n)) : Formula (Var n) := Formula.cmp CompOp.le g (Term.const 0)

@[simp] theorem sat_invLe (g : Term (Var n)) (ω : State (Var n)) :
    Formula.sat (invLe g) ω ↔ Term.eval g ω ≤ 0 := by
  simp only [invLe, Formula.sat, CompOp.interp, Term.eval]

/-- **Base case of the reification.** A certified cover segment — the flow certificate as a
`BoxLe` on the joint evolution domain (`hcert`, from `flow_cert_sound`) — together with the
independence hypothesis `hdisj` and the in-domain right witness `hExist'` (from the cover's
joint-domain co-execution), yields the CSF ∀∃-ODE guarantee over the left/right block programs.

`ρ = Equiv.refl`, so `jointSys = leftBlock ++ rightBlock` directly and the modality's renamed
right program is just `ode rightBlock domR`. -/
theorem segment_faModal (g : Term (Var n)) (fL fR : Fin n → Term (Var n)) (lam : Term (Var n))
    (domL domR : Formula (Var n)) (ν : State (Var n))
    (hdisj : Disjoint ((leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
                      ((rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars))
    (hφL : domL.fv ⊆ (leftBlock fL).boundSet ∪ (leftBlock fL).readVars)
    (hφR : domR.fv ⊆ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars)
    (hcert : BoxLe (Program.ode (jointSys fL fR lam) (Formula.and domL domR))
        (fun ω => Term.eval g ω) ν)
    (hExist : ∀ (s : ℝ) (ΦL : ℝ → State (Var n)), 0 ≤ s → ΦL 0 = ν →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ leftBlock fL,
            HasDerivWithinAt (fun u => ΦL u p.1) (p.2.eval (ΦL t)) (Icc 0 s) t) →
        (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (leftBlock fL).bound → ΦL t x = ν x) →
        (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domL (ΦL t)) →
        ∃ ΦR : ℝ → State (Var n), ΦR 0 = ΦL s ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ p ∈ rightBlock fR lam,
              HasDerivWithinAt (fun u => ΦR u p.1) (p.2.eval (ΦR t)) (Icc 0 s) t) ∧
          (∀ t ∈ Icc (0 : ℝ) s, ∀ x, x ∉ (rightBlock fR lam).bound → ΦR t x = ΦL s x) ∧
          (∀ t ∈ Icc (0 : ℝ) s, Formula.sat domR (ΦR t))) :
    Formula.sat (faModal (Equiv.refl (Var n))
      (Program.ode (leftBlock fL) domL) (Program.ode (rightBlock fR lam) domR) (invLe g)) ν := by
  -- `ρ = id` collapses all renamings; rewrite the goal/hyps to the `faModal_ODE_G'` shape.
  have hjoint : jointSys fL fR lam = leftBlock fL ++ (rightBlock fR lam).rename (Equiv.refl _) := by
    rw [ODESystem.rename_refl]; exact jointSys_split fL fR lam
  refine faModal_ODE_G' (Equiv.refl (Var n)) (leftBlock fL) (rightBlock fR lam)
    domL domR (invLe g) ν ?_ ?_ ?_ ?_ ?_
  · -- hdisj
    rw [ODESystem.rename_refl]; exact hdisj
  · -- hφL
    exact hφL
  · -- hφR (φy.rename id = φy)
    rw [Formula.rename_refl, ODESystem.rename_refl]; exact hφR
  · -- hP2 : box over the joint program of (g≤0), from the BoxLe flow certificate
    rw [ODESystem.rename_refl, Formula.rename_refl, ← jointSys_split]
    rw [sat_box]
    intro ω hω
    rw [sat_invLe]
    exact hcert ω hω
  · -- hExist' : same shape, right domain `domR.rename id = domR`
    rw [ODESystem.rename_refl, Formula.rename_refl]
    exact hExist

end RelCertifier

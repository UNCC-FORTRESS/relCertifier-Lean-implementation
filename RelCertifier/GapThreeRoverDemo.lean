/-
GAP 3 — non-vacuity demonstration at concrete `rover_position` data.

The `mv`-freshness restatement (`MvFrozen`) is only meaningful if it is **satisfiable** at concrete
data — otherwise the theorem instantiation is vacuous (a False antecedent), the trap that also caught
the GAP-2 shared-`Gj` bug. This file proves that for a concrete `rover_position`-shape configuration
(physical coordinates `px`, `vx` + one **frozen mode coordinate**), the `mv`-freshness hypotheses hold
**jointly** — `mv` is a real coordinate the dynamics freeze, carrying the mode index. So a concrete
instantiation is **non-vacuous**.

Coordinates (`Fin 3`): index 0 = `px`, 1 = `vx`, 2 = the auxiliary mode index (frozen). The mode
variable is `mv := Lv 2` — a left coordinate whose field is `const 0` (frozen), not read by the
invariant, and (being `Side.L`) disjoint from the right block's coordinates (`Side.R`).
-/
import RelCertifier.BridgeUnit1
import RelCertifier.Reify

namespace RelCertifier
open DL

/-- Left field of a rover flow mode: `px' = vx`, `vx' = 0.2`, mode coord frozen (`= 0`). -/
noncomputable def roverFL : Fin 3 → Term (Var 3)
  | 0 => Term.var (Lv 1)          -- px' = vx
  | 1 => Term.const (2/10)        -- vx' = 0.2
  | 2 => Term.const 0             -- mode coordinate: frozen

/-- Right field of a rover mode: `px' = vx`, `vx' = 0.4`, mode coord frozen. -/
noncomputable def roverFR : Fin 3 → Term (Var 3)
  | 0 => Term.var (Rv 1)          -- px' = vx
  | 1 => Term.const (4/10)        -- vx' = 0.4
  | 2 => Term.const 0

/-- The relational invariant component `g = px_L - px_R` (reads only `px_L`, `px_R`). -/
def roverG : Term (Var 3) :=
  Term.binop AOp.add (Term.var (Lv 0)) (Term.var (Rv 0))

/-- **The mode variable is the frozen coordinate `Lv 2`.** -/
def roverMv : Var 3 := Lv 2

/-- Every coordinate the right block reads or writes is on the right side (`Side.R`). -/
theorem rightBlock_side_R (fR : Fin 3 → Term (Var 3)) (lam : Term (Var 3))
    (hlam : lam.fv ⊆ {x | x.1 = Side.R}) (hfR : ∀ i, (fR i).fv ⊆ {x | x.1 = Side.R})
    {v : Var 3} (hv : v ∈ (rightBlock fR lam).boundSet ∪ (rightBlock fR lam).readVars) :
    v.1 = Side.R := by
  rcases hv with hb | hr
  · -- bound: v = Rv i
    simp only [ODESystem.boundSet, rightBlock, ODESystem.bound, List.map_map, Set.mem_setOf_eq,
      List.mem_map, Function.comp] at hb
    obtain ⟨i, -, rfl⟩ := hb; rfl
  · -- read: v ∈ (lam * fR i).fv ⊆ Side.R
    simp only [ODESystem.readVars, rightBlock, Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨p, ⟨i, -, rfl⟩, hx⟩ := hr
    simp only [Term.fv, Set.mem_union] at hx
    exact hx.elim (fun h => hlam h) (fun h => hfR i h)

/-- **Non-vacuity at concrete `rover_position` data.** The three `mv`-freshness hypotheses hold
jointly for `mv := Lv 2`:
* `MvFrozen roverFL mv` — `mv` is the frozen mode coordinate (`roverFL 2 = const 0`);
* `mv ∉ roverG.fv` — the invariant reads `px_L`, `px_R`, not the mode coordinate;
* `mv ∉ (rightBlock roverFR 1).boundSet ∪ readVars` — `mv` is `Side.L`, the right block is all
  `Side.R`.
So a concrete instantiation is **non-vacuous** — `mv` is a real coordinate, satisfiable, not the
unsatisfiable `∉ leftBlock.bound ∧ ∉ rightBlock.bound` the coarse formulation demanded. -/
theorem rover_mv_fresh_satisfiable :
    MvFrozen roverFL roverMv ∧
    roverMv ∉ roverG.fv ∧
    roverMv ∉ (rightBlock roverFR (Term.const 1)).boundSet ∪
              (rightBlock roverFR (Term.const 1)).readVars := by
  refine ⟨⟨2, rfl, rfl⟩, ?_, ?_⟩
  · -- Lv 2 ∉ {Lv 0, Rv 0}
    simp only [roverG, roverMv, Term.fv, Set.mem_union, Set.mem_singleton_iff, Lv, Rv]
    decide
  · -- Lv 2 is Side.L, but every right-block coordinate is Side.R
    intro hv
    have : roverMv.1 = Side.R := rightBlock_side_R roverFR (Term.const 1)
      (by simp [Term.fv]) (by intro i; fin_cases i <;> simp [roverFR, Term.fv, Rv]) hv
    exact absurd this (by simp [roverMv, Lv])

end RelCertifier

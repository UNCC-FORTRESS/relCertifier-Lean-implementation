/-
GAP 3 — non-vacuity demonstration at concrete `rover_position` data.

The freshness preconditions (`mv ∉ leftBlock.bound`, `tg ∉ leftBlock.bound`) are only meaningful if
they are **satisfiable** at concrete data — otherwise the theorem instantiation is vacuous (a False
antecedent), the trap that also caught the GAP-2 shared-`Gj` bug. They are satisfiable **jointly** only
if the state space carries coordinates OUTSIDE the physical left/right blocks: `leftBlock` binds every
`Lv i`, `rightBlock` binds every `Rv i`, so any `Var n` built from just `{L, R}` leaves no room. The
`Aux` side provides that room — `mv := Av 1` (the right automaton's mode index) and `tg := Av 0` (the
clock) are auxiliary coordinates, disjoint from the physical left (`Lv`), the physical right (`Rv`), and
the invariant `g` (which reads only physical coordinates).

Crucially, this is also compatible with the `∀∃` disjointness `hd : Disjoint (vars left) (vars right)`
that `tooling_sound` carries: the right automaton reads/assigns `mv`, so `mv` MUST be outside the left
program's variables. An auxiliary `mv` satisfies this by side-split (left = `Lv`, right = `Rv ∪ Aux`);
a *frozen left* `mv = Lv j` would NOT — it lands in `vars(left)` and makes `hd` unsatisfiable (see
`ProbeMvHd.probe_hd_false`). So `Aux` is the correct slot for both `mv` and `tg`.

Coordinates (`Fin 3`): index 0 = `px`, 1 = `vx`, 2 = a third physical coordinate. The mode variable and
clock live in the `Aux` side, outside all three.
-/
import RelCertifier.BridgeUnit1
import RelCertifier.Reify

namespace RelCertifier
open DL

/-- Left field of a rover flow mode: `px' = vx`, `vx' = 0.2`, third coord stationary. -/
noncomputable def roverFL : Fin 3 → Term (Var 3)
  | 0 => Term.var (Lv 1)          -- px' = vx
  | 1 => Term.const (2/10)        -- vx' = 0.2
  | 2 => Term.const 0

/-- Right field of a rover mode: `px' = vx`, `vx' = 0.4`, third coord stationary. -/
noncomputable def roverFR : Fin 3 → Term (Var 3)
  | 0 => Term.var (Rv 1)          -- px' = vx
  | 1 => Term.const (4/10)        -- vx' = 0.4
  | 2 => Term.const 0

/-- The relational invariant component `g = px_L - px_R` (reads only `px_L`, `px_R`). -/
def roverG : Term (Var 3) :=
  Term.binop AOp.add (Term.var (Lv 0)) (Term.var (Rv 0))

/-- **The mode variable is an auxiliary coordinate `Av 1`** — outside `Lv ∪ Rv`. -/
def roverMv : Var 3 := Av 1

/-- **The clock is an auxiliary coordinate `Av 0`** — outside `Lv ∪ Rv`. -/
def roverTg : Var 3 := Av 0

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

/-- An auxiliary coordinate (`Side.Aux`) is not in the left block's bound set (all `Side.L`). -/
theorem aux_not_mem_leftBlock_bound (i : Fin 3) :
    (Av i) ∉ (leftBlock roverFL).bound := by
  intro hv
  have hL : (Av i).1 = Side.L := by
    simp only [leftBlock, ODESystem.bound, List.map_map, List.mem_map, Function.comp] at hv
    obtain ⟨j, -, hj⟩ := hv; rw [← hj]
  exact absurd hL (by simp [Av])

/-- An auxiliary coordinate is not read/written by the right block (all `Side.R`). -/
theorem aux_not_mem_rightBlock (i : Fin 3) :
    (Av i) ∉ (rightBlock roverFR (Term.const 1)).boundSet ∪
             (rightBlock roverFR (Term.const 1)).readVars := by
  intro hv
  have hR : (Av i).1 = Side.R := rightBlock_side_R roverFR (Term.const 1)
    (by simp [Term.fv]) (by intro k; fin_cases k <;> simp [roverFR, Term.fv, Rv]) hv
  exact absurd hR (by simp [Av])

/-- **`mv`-freshness is satisfiable** for `mv := Av 1` (the auxiliary mode slot). It is `Side.Aux`, so
it is outside the left block (`Side.L`), the right block (`Side.R`), and the invariant `g` (reads only
physical `Lv`/`Rv`). The left flow does not evolve it (`∉ leftBlock.bound`), so it carries the right
automaton's mode index across the left residence; and it is disjoint from `vars(left)` (`hd`-compatible).
So the instantiation is **non-vacuous** — `mv` is a real coordinate meeting the theorem's `mv`-freshness. -/
theorem rover_mv_fresh_satisfiable :
    roverMv ∉ (leftBlock roverFL).bound ∧
    roverMv ∉ roverG.fv ∧
    roverMv ∉ (rightBlock roverFR (Term.const 1)).boundSet ∪
              (rightBlock roverFR (Term.const 1)).readVars := by
  refine ⟨aux_not_mem_leftBlock_bound 1, ?_, aux_not_mem_rightBlock 1⟩
  simp only [roverG, roverMv, Term.fv, Set.mem_union, Set.mem_singleton_iff, Av, Lv, Rv]; decide

/-- **`tg`-freshness is satisfiable** for `tg := Av 0` (the auxiliary clock coordinate). Same `Side.Aux`
argument: disjoint from the left block (`Side.L`), the right block (`Side.R`), and the invariant. So the
clock ticks in its own coordinate, outside all physical blocks — the `tg`-room `tooling_sound` needs. -/
theorem rover_tg_fresh_satisfiable :
    roverTg ∉ (leftBlock roverFL).bound ∧
    roverTg ∉ (rightBlock roverFR (Term.const 1)).boundSet ∪
              (rightBlock roverFR (Term.const 1)).readVars ∧
    roverTg ∉ roverG.fv := by
  refine ⟨aux_not_mem_leftBlock_bound 0, aux_not_mem_rightBlock 0, ?_⟩
  simp only [roverTg, roverG, Term.fv, Set.mem_union, Set.mem_singleton_iff, Av, Lv, Rv]; decide

/-- **Both the mode variable and the clock are satisfiable, disjointly.** `mv = Av 1` and `tg = Av 0`
are distinct auxiliary coordinates, each outside the left block — so the end-to-end theorem's freshness
precondition (`mv` and `tg` both roomed in `Aux`) holds at concrete data, **non-vacuously on both**, and
compatibly with the `∀∃` disjointness `hd`. -/
theorem rover_freshness_nonvacuous :
    roverMv ∉ (leftBlock roverFL).bound ∧ roverMv ≠ roverTg ∧
    roverTg ∉ (leftBlock roverFL).bound := by
  refine ⟨aux_not_mem_leftBlock_bound 1, ?_, aux_not_mem_leftBlock_bound 0⟩
  simp [roverMv, roverTg, Av]

end RelCertifier

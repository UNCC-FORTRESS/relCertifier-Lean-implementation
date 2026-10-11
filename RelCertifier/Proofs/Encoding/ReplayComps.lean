/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The tool's invariant components are the carried-over instances' row atoms

The emitted cover's packs (`modalVerdX`, `modalVerdDynX`) quote the declared row's components
as the tool lowers them (`Oracle.invComponents`, flattening the conjunction). The carried-over
instances state their rows atom by atom (`Run.invToG` of each conjunct, `gAt i`). For a row
that is a conjunction of comparisons, every one of which lowers, the two lists are the same
(`hostComps_atoms`), so a replay can use the packs at the statement's own rows.

New leaf; no upstream edits.
-/
import RelCertifier.Proofs.Encoding.CoverInstance

namespace RelCertifier

open DL Parse

variable {n : ℕ}

/-- The conjuncts of a row (the carried-over instances' `atomsOf`). -/
def pAtoms : PForm → List PForm
  | .and x y => pAtoms x ++ pAtoms y
  | f => [f]

/-- A conjunct is a comparison whose lowering succeeds. -/
def CmpLowers (vars : List String) (n : ℕ) (a : PForm) : Prop :=
  (∃ op x y, a = .cmp op x y) ∧ (Run.invToG vars n a).isSome = true

theorem invComponents_cmp (vars : List String) (op : String) (x y : PExpr) :
    Oracle.invComponents vars n (.cmp op x y) =
      (Run.invToG vars n (.cmp op x y)).map (fun t => [t]) := by
  simp only [Oracle.invComponents, Run.invToG]
  split_ifs <;>
    rcases Run.lowerE vars n Side.L x with _ | ex <;>
    rcases Run.lowerE vars n Side.L y with _ | ey <;> rfl

/-- **The tool's components of a conjunction of comparisons are its conjuncts' lowerings.** -/
theorem invComponents_atoms (vars : List String) :
    ∀ f : PForm, (∀ a ∈ pAtoms f, CmpLowers vars n a) →
      Oracle.invComponents vars n f =
        some ((pAtoms f).map (fun a => (Run.invToG vars n a).getD (ITerm.rat 0))) := by
  intro f
  induction f with
  | tt =>
      intro h
      obtain ⟨⟨op, x, y, hxy⟩, -⟩ := h .tt (by simp [pAtoms])
      cases hxy
  | cmp op x y =>
      intro h
      obtain ⟨-, hs⟩ := h (.cmp op x y) (by simp [pAtoms])
      rw [invComponents_cmp]
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
      simp [pAtoms, ht]
  | and x y ihx ihy =>
      intro h
      have hx := ihx (fun a ha => h a (by simp [pAtoms, ha]))
      have hy := ihy (fun a ha => h a (by simp [pAtoms, ha]))
      simp only [Oracle.invComponents, hx, hy, Option.bind_eq_bind, Option.bind_some,
        pAtoms, List.map_append]
  | or x y _ _ =>
      intro h
      obtain ⟨⟨op, x', y', hxy⟩, -⟩ := h (.or x y) (by simp [pAtoms])
      cases hxy
  | not x _ =>
      intro h
      obtain ⟨⟨op, x', y', hxy⟩, -⟩ := h (.not x) (by simp [pAtoms])
      cases hxy

/-- **Host form**: the components the packs quote are the conjuncts' host terms. -/
theorem hostComps_atoms (vars : List String) (f : PForm)
    (h : ∀ a ∈ pAtoms f, CmpLowers vars n a) :
    hostComps vars n f =
      (pAtoms f).map (fun a => ((Run.invToG vars n a).map ITerm.toHost).getD (Term.const 0)) := by
  unfold hostComps
  rw [invComponents_atoms vars f h]
  simp only [Option.map_some, Option.getD_some, List.map_map]
  refine List.map_congr_left (fun a ha => ?_)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h a ha).2
  simp [ht]

end RelCertifier

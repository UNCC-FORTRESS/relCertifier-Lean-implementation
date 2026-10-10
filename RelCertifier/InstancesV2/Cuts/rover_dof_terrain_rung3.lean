/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung3` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_dof_terrain_rung3`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_dof_terrain_rung3

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_dof_terrain_rung3_cutsV2 : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

def rover_dof_terrain_rung3_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.65")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_dof_terrain_rung3_cutsV2_wf : evolStrengtheningWF rover_dof_terrain_rung3_IRv2 rover_dof_terrain_rung3_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_dof_terrain_rung3_cutsV2X_wf : evolStrengtheningWFX rover_dof_terrain_rung3_IRv2 rover_dof_terrain_rung3_cutsV2X = true := rfl

end RelCertifier.Oracle

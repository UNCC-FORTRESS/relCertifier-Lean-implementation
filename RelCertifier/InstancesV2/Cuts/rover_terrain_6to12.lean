/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to12` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_6to12`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_terrain_6to12

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_terrain_6to12_cutsV2 : EvolStrengthening :=
  { L := [
      ("MUD", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.25")), CutRoute.shape), ((.cmp ">=" (.var "gamma") (.num "0.02")), CutRoute.frozen)]),
      ("GRAVEL", [((.cmp ">=" (.var "s") (.num "5.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.45")), CutRoute.shape)]),
      ("PAVED", [((.cmp ">=" (.var "s") (.num "12.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.7")), CutRoute.shape)])
    ]
    R := [
      ("MUD", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.25")), CutRoute.shape)]),
      ("GRAVEL", [((.cmp ">=" (.var "s") (.num "5.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.45")), CutRoute.shape)]),
      ("PAVED", [((.cmp ">=" (.var "s") (.num "12.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "0.7")), CutRoute.shape)])
    ] }

def rover_terrain_6to12_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("MUD", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.25")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "gamma") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GRAVEL", [⟨(.cmp ">=" (.var "s") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.45")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("PAVED", [⟨(.cmp ">=" (.var "s") (.num "12.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("MUD", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.25")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("GRAVEL", [⟨(.cmp ">=" (.var "s") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.45")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("PAVED", [⟨(.cmp ">=" (.var "s") (.num "12.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "0.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_terrain_6to12_cutsV2_wf : evolStrengtheningWF rover_terrain_6to12_IRv2 rover_terrain_6to12_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_terrain_6to12_cutsV2X_wf : evolStrengtheningWFX rover_terrain_6to12_IRv2 rover_terrain_6to12_cutsV2X = true := rfl

end RelCertifier.Oracle

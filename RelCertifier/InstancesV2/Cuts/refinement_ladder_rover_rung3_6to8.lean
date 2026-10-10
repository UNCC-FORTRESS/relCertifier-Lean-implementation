/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung3_6to8`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.refinement_ladder_rover_rung3_6to8

namespace RelCertifier.Oracle

open RelCertifier.Parse

def refinement_ladder_rover_rung3_6to8_cutsV2 : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

def refinement_ladder_rover_rung3_6to8_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.65")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.65")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem refinement_ladder_rover_rung3_6to8_cutsV2_wf : evolStrengtheningWF refinement_ladder_rover_rung3_6to8_IRv2 refinement_ladder_rover_rung3_6to8_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem refinement_ladder_rover_rung3_6to8_cutsV2X_wf : evolStrengtheningWFX refinement_ladder_rover_rung3_6to8_IRv2 refinement_ladder_rover_rung3_6to8_cutsV2X = true := rfl

end RelCertifier.Oracle

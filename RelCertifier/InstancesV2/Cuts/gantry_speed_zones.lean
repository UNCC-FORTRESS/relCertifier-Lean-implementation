/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `gantry_speed_zones` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py gantry_speed_zones`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.gantry_speed_zones

namespace RelCertifier.Oracle

open RelCertifier.Parse

def gantry_speed_zones_cutsV2 : EvolStrengthening :=
  { L := [
      ("FREE", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.shape), ((.cmp ">=" (.var "y") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "y") (.num "0.5")), CutRoute.shape)]),
      ("APPROACH", [((.cmp ">=" (.var "x") (.num "0.3")), CutRoute.shape), ((.cmp ">=" (.var "y") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "y") (.num "0.5")), CutRoute.shape)]),
      ("PLACE", [((.cmp ">=" (.var "x") (.num "0.45")), CutRoute.shape), ((.cmp "<=" (.var "x") (.num "0.8")), CutRoute.shape), ((.cmp ">=" (.var "y") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "y") (.num "0.5")), CutRoute.shape)])
    ]
    R := [
      ("MOVE", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "x") (.num "0.8")), CutRoute.shape), ((.cmp ">=" (.var "y") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "y") (.num "0.5")), CutRoute.shape)])
    ] }

def gantry_speed_zones_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("FREE", [⟨(.cmp ">=" (.var "x") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "y") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "y") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "0.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("APPROACH", [⟨(.cmp ">=" (.var "x") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "y") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "y") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "0.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("PLACE", [⟨(.cmp ">=" (.var "x") (.num "0.45")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "0.8")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "y") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "y") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("MOVE", [⟨(.cmp ">=" (.var "x") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "0.8")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "y") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "y") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem gantry_speed_zones_cutsV2_wf : evolStrengtheningWF gantry_speed_zones_IRv2 gantry_speed_zones_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem gantry_speed_zones_cutsV2X_wf : evolStrengtheningWFX gantry_speed_zones_IRv2 gantry_speed_zones_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `zone_lightmass_schedule` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py zone_lightmass_schedule`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.zone_lightmass_schedule

namespace RelCertifier.Oracle

open RelCertifier.Parse

def zone_lightmass_schedule_cutsV2 : EvolStrengthening :=
  { L := [
      ("COMFORT", [((.cmp ">=" (.var "T") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "30.0")), CutRoute.shape)]),
      ("ECONOMY", [((.cmp ">=" (.var "T") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "30.0")), CutRoute.shape)])
    ]
    R := [
      ("COMFORT", [((.cmp ">=" (.var "T") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "30.0")), CutRoute.shape)]),
      ("STANDBY", [((.cmp ">=" (.var "T") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "30.0")), CutRoute.shape)]),
      ("ECONOMY", [((.cmp ">=" (.var "T") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "30.0")), CutRoute.shape)])
    ] }

def zone_lightmass_schedule_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("COMFORT", [⟨(.cmp ">=" (.var "T") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("ECONOMY", [⟨(.cmp ">=" (.var "T") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("COMFORT", [⟨(.cmp ">=" (.var "T") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("STANDBY", [⟨(.cmp ">=" (.var "T") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("ECONOMY", [⟨(.cmp ">=" (.var "T") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem zone_lightmass_schedule_cutsV2_wf : evolStrengtheningWF zone_lightmass_schedule_IRv2 zone_lightmass_schedule_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem zone_lightmass_schedule_cutsV2X_wf : evolStrengtheningWFX zone_lightmass_schedule_IRv2 zone_lightmass_schedule_cutsV2X = true := rfl

end RelCertifier.Oracle

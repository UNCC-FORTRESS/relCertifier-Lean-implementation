/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `csf21_vehicle_bus` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py csf21_vehicle_bus`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.csf21_vehicle_bus

namespace RelCertifier.Oracle

open RelCertifier.Parse

def csf21_vehicle_bus_cutsV2 : EvolStrengthening :=
  { L := [
      ("AccCool", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("AccHeat", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("CoastCool", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("CoastHeat", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("BrkCool", []),
      ("BrkHeat", [])
    ]
    R := [
      ("AccCoolA", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("AccCoolT", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("AccHeatA", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("AccHeatT", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("CoastCoolA", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("CoastCoolT", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("CoastHeatA", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("CoastHeatT", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen)]),
      ("BrkCoolA", []),
      ("BrkCoolT", []),
      ("BrkHeatA", []),
      ("BrkHeatT", [])
    ] }

def csf21_vehicle_bus_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("AccCool", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccHeat", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastCool", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CoastHeat", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BrkCool", []),
      ("BrkHeat", [])
    ]
    R := [
      ("AccCoolA", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccCoolT", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccHeatA", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccHeatT", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastCoolA", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CoastCoolT", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CoastHeatA", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CoastHeatT", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BrkCoolA", []),
      ("BrkCoolT", []),
      ("BrkHeatA", []),
      ("BrkHeatT", [])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem csf21_vehicle_bus_cutsV2_wf : evolStrengtheningWF csf21_vehicle_bus_IRv2 csf21_vehicle_bus_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem csf21_vehicle_bus_cutsV2X_wf : evolStrengtheningWFX csf21_vehicle_bus_IRv2 csf21_vehicle_bus_cutsV2X = true := rfl

end RelCertifier.Oracle

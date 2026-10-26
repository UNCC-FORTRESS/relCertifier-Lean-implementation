/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hvac_fan_staging` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py hvac_fan_staging`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.hvac_fan_staging

namespace RelCertifier.Oracle

open RelCertifier.Parse

def hvac_fan_staging_cutsV2 : EvolStrengthening :=
  { L := [
      ("LOW", [((.cmp ">=" (.var "T") (.num "16.0")), CutRoute.shape)]),
      ("MED", [((.cmp ">=" (.var "T") (.num "23.5")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "24.5")), CutRoute.shape)]),
      ("HIGH", [((.cmp "<=" (.var "T") (.num "32.0")), CutRoute.shape)])
    ]
    R := [
      ("LOW", [((.cmp ">=" (.var "T") (.num "16.0")), CutRoute.shape)]),
      ("MED", [((.cmp ">=" (.var "T") (.num "16.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "32.0")), CutRoute.shape)]),
      ("HIGH", [((.cmp "<=" (.var "T") (.num "32.0")), CutRoute.shape)])
    ] }

def hvac_fan_staging_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("LOW", [⟨(.cmp ">=" (.var "T") (.num "16.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "27.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("MED", [⟨(.cmp ">=" (.var "T") (.num "23.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "24.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("HIGH", [⟨(.cmp "<=" (.var "T") (.num "32.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "T") (.num "21.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("LOW", [⟨(.cmp ">=" (.var "T") (.num "16.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "27.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("MED", [⟨(.cmp ">=" (.var "T") (.num "16.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "32.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("HIGH", [⟨(.cmp "<=" (.var "T") (.num "32.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "T") (.num "21.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem hvac_fan_staging_cutsV2_wf : evolStrengtheningWF hvac_fan_staging_IRv2 hvac_fan_staging_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem hvac_fan_staging_cutsV2X_wf : evolStrengtheningWFX hvac_fan_staging_IRv2 hvac_fan_staging_cutsV2X = true := rfl

end RelCertifier.Oracle

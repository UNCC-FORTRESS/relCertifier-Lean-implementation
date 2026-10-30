/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `boiler_purge_vfd` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py boiler_purge_vfd`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.boiler_purge_vfd

namespace RelCertifier.Oracle

open RelCertifier.Parse

def boiler_purge_vfd_cutsV2 : EvolStrengthening :=
  { L := [
      ("PURGE", []),
      ("FIRE", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.frozen)])
    ]
    R := [
      ("PURGE", []),
      ("FIRE", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.frozen)])
    ] }

def boiler_purge_vfd_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("PURGE", []),
      ("FIRE", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("PURGE", []),
      ("FIRE", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem boiler_purge_vfd_cutsV2_wf : evolStrengtheningWF boiler_purge_vfd_IRv2 boiler_purge_vfd_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem boiler_purge_vfd_cutsV2X_wf : evolStrengtheningWFX boiler_purge_vfd_IRv2 boiler_purge_vfd_cutsV2X = true := rfl

end RelCertifier.Oracle

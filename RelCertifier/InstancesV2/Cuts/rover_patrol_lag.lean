/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_lag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_lag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_patrol_lag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_patrol_lag_cutsV2 : EvolStrengthening :=
  { L := [
      ("SLOW", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_ECO", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_BRISK", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("FAST", [((.cmp ">=" (.var "s") (.num "50.0")), CutRoute.diNonstrict)])
    ]
    R := [
      ("SLOW", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_ECO", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_BRISK", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("FAST", [((.cmp ">=" (.var "s") (.num "50.0")), CutRoute.diNonstrict)])
    ] }

def rover_patrol_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("SLOW", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MEDIUM_ECO", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MEDIUM_BRISK", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FAST", [⟨(.cmp ">=" (.var "s") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ]
    R := [
      ("SLOW", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MEDIUM_ECO", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MEDIUM_BRISK", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FAST", [⟨(.cmp ">=" (.var "s") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_patrol_lag_cutsV2_wf : evolStrengtheningWF rover_patrol_lag_IRv2 rover_patrol_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_patrol_lag_cutsV2X_wf : evolStrengtheningWFX rover_patrol_lag_IRv2 rover_patrol_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

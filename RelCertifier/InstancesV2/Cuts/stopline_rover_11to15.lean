/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_rover_11to15` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_rover_11to15`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.stopline_rover_11to15

namespace RelCertifier.Oracle

open RelCertifier.Parse

def stopline_rover_11to15_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.35")), CutRoute.frozen)]),
      ("BRAKE", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.diNonstrict)]),
      ("STOP", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.35")), CutRoute.frozen)])
    ]
    R := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.35")), CutRoute.frozen)]),
      ("BRAKE", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.diNonstrict)]),
      ("STOP", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.35")), CutRoute.frozen)])
    ] }

def stopline_rover_11to15_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BRAKE", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BRAKE", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem stopline_rover_11to15_cutsV2_wf : evolStrengtheningWF stopline_rover_11to15_IRv2 stopline_rover_11to15_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem stopline_rover_11to15_cutsV2X_wf : evolStrengtheningWFX stopline_rover_11to15_IRv2 stopline_rover_11to15_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_payload` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_payload`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_rollover_payload

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_rollover_payload_cutsV2 : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "3.0")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "60.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "5.0")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "140.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "6.5")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "58.0")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "138.0")), CutRoute.diNonstrict)])
    ] }

def rover_rollover_payload_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "3.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "140.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "6.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "58.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_rollover_payload_cutsV2_wf : evolStrengtheningWF rover_rollover_payload_IRv2 rover_rollover_payload_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_rollover_payload_cutsV2X_wf : evolStrengtheningWFX rover_rollover_payload_IRv2 rover_rollover_payload_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_accel_copy` (choice exhibit) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.Choice.BenchIR.vehicle_accel_copy

namespace RelCertifier.Oracle

open RelCertifier.Parse

def vehicle_accel_copy_cutsC : EvolStrengthening :=
  { L := [
      ("Accel", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Coast", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "30.0")), CutRoute.frozen)]),
      ("Brake", [((.cmp "<=" (.var "v") (.num "30.0")), CutRoute.diStrict)])
    ]
    R := [
      ("Accel", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Coast", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "30.0")), CutRoute.frozen)]),
      ("Brake", [((.cmp "<=" (.var "v") (.num "30.0")), CutRoute.diStrict)])
    ] }

def vehicle_accel_copy_cutsCX : EvolStrengtheningX :=
  { L := [
      ("Accel", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Coast", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Brake", [⟨(.cmp "<=" (.var "v") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("Accel", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Coast", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Brake", [⟨(.cmp "<=" (.var "v") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem vehicle_accel_copy_cutsC_wf : evolStrengtheningWF vehicle_accel_copy_IRc vehicle_accel_copy_cutsC = true := rfl

/-- The extended certificate is well formed. -/
theorem vehicle_accel_copy_cutsCX_wf : evolStrengtheningWFX vehicle_accel_copy_IRc vehicle_accel_copy_cutsCX = true := rfl

end RelCertifier.Oracle

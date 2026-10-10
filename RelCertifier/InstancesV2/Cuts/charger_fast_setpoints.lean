/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py charger_fast_setpoints`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.charger_fast_setpoints

namespace RelCertifier.Oracle

open RelCertifier.Parse

def charger_fast_setpoints_cutsV2 : EvolStrengthening :=
  { L := [
      ("BULK", [((.cmp ">=" (.var "x") (.num "15.0")), CutRoute.shape)]),
      ("ABSORB", [((.cmp ">=" (.var "x") (.num "80.0")), CutRoute.shape)]),
      ("FULL", [((.cmp ">=" (.var "x") (.num "99.0")), CutRoute.frozen)])
    ]
    R := [
      ("BULK", [((.cmp ">=" (.var "x") (.num "15.0")), CutRoute.shape)]),
      ("ABSORB", [((.cmp ">=" (.var "x") (.num "80.0")), CutRoute.shape)]),
      ("FULL", [((.cmp ">=" (.var "x") (.num "99.0")), CutRoute.frozen)]),
      ("FAULT", [])
    ] }

def charger_fast_setpoints_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("BULK", [⟨(.cmp ">=" (.var "x") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "90.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("ABSORB", [⟨(.cmp ">=" (.var "x") (.num "80.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "100.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("FULL", [⟨(.cmp ">=" (.var "x") (.num "99.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("BULK", [⟨(.cmp ">=" (.var "x") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "90.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("ABSORB", [⟨(.cmp ">=" (.var "x") (.num "80.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "100.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("FULL", [⟨(.cmp ">=" (.var "x") (.num "99.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("FAULT", [⟨(.cmp "<=" (.var "x") (.num "10.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem charger_fast_setpoints_cutsV2_wf : evolStrengtheningWF charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem charger_fast_setpoints_cutsV2X_wf : evolStrengtheningWFX charger_fast_setpoints_IRv2 charger_fast_setpoints_cutsV2X = true := rfl

end RelCertifier.Oracle

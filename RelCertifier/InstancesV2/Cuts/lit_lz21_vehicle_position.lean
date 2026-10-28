/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_lz21_vehicle_position` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_lz21_vehicle_position`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.lit_lz21_vehicle_position

namespace RelCertifier.Oracle

open RelCertifier.Parse

def lit_lz21_vehicle_position_cutsV2 : EvolStrengthening :=
  { L := [
      ("Um", [((.cmp "<=" (.var "v") (.num "0.1")), CutRoute.diStrict)]),
      ("U0", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.1")), CutRoute.frozen)]),
      ("Up", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("Um", [((.cmp "<=" (.var "v") (.num "0.1")), CutRoute.diStrict)]),
      ("U0", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.1")), CutRoute.frozen)]),
      ("Up", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)])
    ] }

def lit_lz21_vehicle_position_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Um", [⟨(.cmp "<=" (.var "v") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("U0", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Up", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("Um", [⟨(.cmp "<=" (.var "v") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("U0", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Up", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem lit_lz21_vehicle_position_cutsV2_wf : evolStrengtheningWF lit_lz21_vehicle_position_IRv2 lit_lz21_vehicle_position_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem lit_lz21_vehicle_position_cutsV2X_wf : evolStrengtheningWFX lit_lz21_vehicle_position_IRv2 lit_lz21_vehicle_position_cutsV2X = true := rfl

end RelCertifier.Oracle

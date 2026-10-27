/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `furnace_program_timebase` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py furnace_program_timebase`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.furnace_program_timebase

namespace RelCertifier.Oracle

open RelCertifier.Parse

def furnace_program_timebase_cutsV2 : EvolStrengthening :=
  { L := [
      ("PREHEAT", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)]),
      ("HEAT", [((.cmp ">=" (.var "s") (.num "640.0")), CutRoute.shape), ((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)]),
      ("SOAK", [((.cmp ">=" (.var "s") (.num "860.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "870.0")), CutRoute.shape), ((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)])
    ]
    R := [
      ("PREHEAT", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)]),
      ("HEAT", [((.cmp ">=" (.var "s") (.num "640.0")), CutRoute.shape), ((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)]),
      ("SOAK", [((.cmp ">=" (.var "s") (.num "860.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "870.0")), CutRoute.shape), ((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "s") (.num "900.0")), CutRoute.shape)])
    ] }

def furnace_program_timebase_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("PREHEAT", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "650.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("HEAT", [⟨(.cmp ">=" (.var "s") (.num "640.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "870.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("SOAK", [⟨(.cmp ">=" (.var "s") (.num "860.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "870.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("PREHEAT", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "650.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("HEAT", [⟨(.cmp ">=" (.var "s") (.num "640.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "870.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("SOAK", [⟨(.cmp ">=" (.var "s") (.num "860.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "870.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "s") (.num "900.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem furnace_program_timebase_cutsV2_wf : evolStrengtheningWF furnace_program_timebase_IRv2 furnace_program_timebase_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem furnace_program_timebase_cutsV2X_wf : evolStrengtheningWFX furnace_program_timebase_IRv2 furnace_program_timebase_cutsV2X = true := rfl

end RelCertifier.Oracle

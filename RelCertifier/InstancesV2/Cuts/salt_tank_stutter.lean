/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `salt_tank_stutter` (stutter_demo) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_stutter_demo.py`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.salt_tank_stutter

namespace RelCertifier.Oracle

open RelCertifier.Parse

def salt_tank_stutter_cutsV2 : EvolStrengthening :=
  { L := [
      ("On", [((.cmp ">=" (.var "xp") (.num "22.0")), CutRoute.shape)]),
      ("Off", [])
    ]
    R := [
      ("On", [((.cmp ">=" (.var "xp") (.num "25.0")), CutRoute.shape)]),
      ("Off", [])
    ] }

def salt_tank_stutter_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("On", [⟨(.cmp ">=" (.var "xp") (.num "22.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("Off", [⟨(.cmp "<=" (.var "xp") (.num "28.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("On", [⟨(.cmp ">=" (.var "xp") (.num "25.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("Off", [⟨(.cmp "<=" (.var "xp") (.num "25.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem salt_tank_stutter_cutsV2_wf : evolStrengtheningWF salt_tank_stutter_IRv2 salt_tank_stutter_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem salt_tank_stutter_cutsV2X_wf : evolStrengtheningWFX salt_tank_stutter_IRv2 salt_tank_stutter_cutsV2X = true := rfl

end RelCertifier.Oracle

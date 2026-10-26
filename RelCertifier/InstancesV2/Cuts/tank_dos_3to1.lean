/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.tank_dos_3to1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def tank_dos_3to1_cutsV2 : EvolStrengthening :=
  { L := [
      ("HIGH", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape)]),
      ("LOW", [((.cmp "<=" (.var "h") (.num "2.0")), CutRoute.shape)])
    ]
    R := [
      ("HIGH", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape)]),
      ("LOW", [((.cmp "<=" (.var "h") (.num "2.0")), CutRoute.shape)])
    ] }

def tank_dos_3to1_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("HIGH", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "1.3")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("LOW", [⟨(.cmp "<=" (.var "h") (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.7")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("HIGH", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "1.3")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("LOW", [⟨(.cmp "<=" (.var "h") (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.7")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem tank_dos_3to1_cutsV2_wf : evolStrengtheningWF tank_dos_3to1_IRv2 tank_dos_3to1_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem tank_dos_3to1_cutsV2X_wf : evolStrengtheningWFX tank_dos_3to1_IRv2 tank_dos_3to1_cutsV2X = true := rfl

end RelCertifier.Oracle

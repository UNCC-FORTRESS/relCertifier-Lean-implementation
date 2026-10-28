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
      ("P2", [((.cmp ">=" (.var "w") (.num "6.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "h") (.num "2.5")), CutRoute.diStrict)]),
      ("P3", [((.cmp ">=" (.var "w") (.num "10.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)]),
      ("P4", [((.cmp ">=" (.var "w") (.num "14.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)]),
      ("P5", [((.cmp ">=" (.var "w") (.num "18.0")), CutRoute.shape), ((.cmp "<=" (.var "w") (.num "22.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("P2", [((.cmp ">=" (.var "w") (.num "6.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "h") (.num "2.5")), CutRoute.diStrict)]),
      ("P3", [((.cmp ">=" (.var "w") (.num "10.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)]),
      ("P4", [((.cmp ">=" (.var "w") (.num "14.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)]),
      ("P5", [((.cmp ">=" (.var "w") (.num "18.0")), CutRoute.shape), ((.cmp "<=" (.var "w") (.num "22.0")), CutRoute.shape), ((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diStrict)])
    ] }

def tank_dos_3to1_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("P2", [⟨(.cmp ">=" (.var "w") (.num "6.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "h") (.num "2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P3", [⟨(.cmp ">=" (.var "w") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P4", [⟨(.cmp ">=" (.var "w") (.num "14.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P5", [⟨(.cmp ">=" (.var "w") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("P2", [⟨(.cmp ">=" (.var "w") (.num "6.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "h") (.num "2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P3", [⟨(.cmp ">=" (.var "w") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P4", [⟨(.cmp ">=" (.var "w") (.num "14.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("P5", [⟨(.cmp ">=" (.var "w") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "22.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem tank_dos_3to1_cutsV2_wf : evolStrengtheningWF tank_dos_3to1_IRv2 tank_dos_3to1_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem tank_dos_3to1_cutsV2X_wf : evolStrengtheningWFX tank_dos_3to1_IRv2 tank_dos_3to1_cutsV2X = true := rfl

end RelCertifier.Oracle

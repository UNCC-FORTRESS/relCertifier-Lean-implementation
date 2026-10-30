/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `fuelcell_chp_dos` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py fuelcell_chp_dos`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.fuelcell_chp_dos

namespace RelCertifier.Oracle

open RelCertifier.Parse

def fuelcell_chp_dos_cutsV2 : EvolStrengthening :=
  { L := [
      ("LOW", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)]),
      ("MED", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)]),
      ("HIGH", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)])
    ]
    R := [
      ("LOW", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)]),
      ("MED", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)]),
      ("HIGH", [((.cmp ">=" (.var "Tin") (.num "40")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "56")), CutRoute.frozen), ((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "Tin") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "Tin") (.num "100")), CutRoute.frozen)])
    ] }

def fuelcell_chp_dos_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("LOW", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("MED", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("HIGH", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("LOW", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("MED", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("HIGH", [⟨(.cmp ">=" (.var "Tin") (.num "40")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "56")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "Tin") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "Tin") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem fuelcell_chp_dos_cutsV2_wf : evolStrengtheningWF fuelcell_chp_dos_IRv2 fuelcell_chp_dos_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem fuelcell_chp_dos_cutsV2X_wf : evolStrengtheningWFX fuelcell_chp_dos_IRv2 fuelcell_chp_dos_cutsV2X = true := rfl

end RelCertifier.Oracle

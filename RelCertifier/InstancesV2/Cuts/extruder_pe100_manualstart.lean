/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `extruder_pe100_manualstart` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py extruder_pe100_manualstart`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.extruder_pe100_manualstart

namespace RelCertifier.Oracle

open RelCertifier.Parse

def extruder_pe100_manualstart_cutsV2 : EvolStrengthening :=
  { L := [
      ("N1", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N2", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N3", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N4", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)])
    ]
    R := [
      ("N1", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N2", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N3", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)]),
      ("N4", [((.cmp ">=" (.var "p") (.num "0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "300")), CutRoute.frozen), ((.cmp ">=" (.var "p") (.num "180")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "220")), CutRoute.frozen)])
    ] }

def extruder_pe100_manualstart_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("N1", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N2", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N3", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N4", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("N1", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N2", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N3", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("N4", [⟨(.cmp ">=" (.var "p") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "300")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "p") (.num "180")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "220")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem extruder_pe100_manualstart_cutsV2_wf : evolStrengtheningWF extruder_pe100_manualstart_IRv2 extruder_pe100_manualstart_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem extruder_pe100_manualstart_cutsV2X_wf : evolStrengtheningWFX extruder_pe100_manualstart_IRv2 extruder_pe100_manualstart_cutsV2X = true := rfl

end RelCertifier.Oracle

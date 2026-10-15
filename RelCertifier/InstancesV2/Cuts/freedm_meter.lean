/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `freedm_meter` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py freedm_meter`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.freedm_meter

namespace RelCertifier.Oracle

open RelCertifier.Parse

def freedm_meter_cutsV2 : EvolStrengthening :=
  { L := [
      ("BatD0R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("BatD0R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.diStrict)]),
      ("BatD1R0", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("BatD1R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("BatD2R0", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("BatD2R1", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("GridD0R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD0R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD1R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD1R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD2R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD2R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)])
    ]
    R := [
      ("BatD0R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("BatD0R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.diStrict)]),
      ("BatD1R0", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("BatD1R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("BatD2R0", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("BatD2R1", [((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.diStrict)]),
      ("GridD0R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD0R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD1R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD1R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD2R0", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)]),
      ("GridD2R1", [((.cmp ">=" (.var "B") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "B") (.num "10.0")), CutRoute.frozen)])
    ] }

def freedm_meter_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("BatD0R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BatD0R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD1R0", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD1R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BatD2R0", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD2R1", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("GridD0R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD0R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD1R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD1R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD2R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD2R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("BatD0R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BatD0R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD1R0", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD1R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BatD2R0", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BatD2R1", [⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("GridD0R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD0R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD1R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD1R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD2R0", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("GridD2R1", [⟨(.cmp ">=" (.var "B") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "B") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem freedm_meter_cutsV2_wf : evolStrengtheningWF freedm_meter_IRv2 freedm_meter_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem freedm_meter_cutsV2X_wf : evolStrengtheningWFX freedm_meter_IRv2 freedm_meter_cutsV2X = true := rfl

end RelCertifier.Oracle

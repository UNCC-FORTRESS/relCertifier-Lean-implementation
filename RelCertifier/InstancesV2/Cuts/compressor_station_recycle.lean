/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `compressor_station_recycle` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py compressor_station_recycle`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.compressor_station_recycle

namespace RelCertifier.Oracle

open RelCertifier.Parse

def compressor_station_recycle_cutsV2 : EvolStrengthening :=
  { L := [
      ("HIGH", [((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)]),
      ("MED", [((.cmp "<=" (.var "pd") (.num "64.0")), CutRoute.diStrict), ((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)]),
      ("LOW", [((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)])
    ]
    R := [
      ("LOW", [((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)]),
      ("MED", [((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)]),
      ("HIGH", [((.cmp ">=" (.var "ps") (.num "45.0")), CutRoute.diStrict), ((.cmp "<=" (.var "ps") (.num "62.0")), CutRoute.diStrict), ((.cmp ">=" (.var "pd") (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.var "pd") (.num "70.0")), CutRoute.diStrict)])
    ] }

def compressor_station_recycle_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("HIGH", [⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "61.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩]),
      ("MED", [⟨(.cmp "<=" (.var "pd") (.num "64.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("LOW", [⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("LOW", [⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("MED", [⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("HIGH", [⟨(.cmp ">=" (.var "ps") (.num "45.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "ps") (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "pd") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "pd") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem compressor_station_recycle_cutsV2_wf : evolStrengtheningWF compressor_station_recycle_IRv2 compressor_station_recycle_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem compressor_station_recycle_cutsV2X_wf : evolStrengtheningWFX compressor_station_recycle_IRv2 compressor_station_recycle_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `reactor_feed_wireless` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py reactor_feed_wireless`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.reactor_feed_wireless

namespace RelCertifier.Oracle

open RelCertifier.Parse

def reactor_feed_wireless_cutsV2 : EvolStrengthening :=
  { L := [
      ("F1", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F2", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F3", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F4", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)])
    ]
    R := [
      ("F1", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F2", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F3", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("F4", [((.cmp ">=" (.var "T") (.num "15.0")), CutRoute.diStrict), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "p") (.num "15.0")), CutRoute.frozen), ((.cmp "<=" (.var "p") (.num "35.0")), CutRoute.frozen)])
    ] }

def reactor_feed_wireless_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("F1", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F2", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F3", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F4", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("F1", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F2", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F3", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("F4", [⟨(.cmp ">=" (.var "T") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "p") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem reactor_feed_wireless_cutsV2_wf : evolStrengtheningWF reactor_feed_wireless_IRv2 reactor_feed_wireless_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem reactor_feed_wireless_cutsV2X_wf : evolStrengtheningWFX reactor_feed_wireless_IRv2 reactor_feed_wireless_cutsV2X = true := rfl

end RelCertifier.Oracle

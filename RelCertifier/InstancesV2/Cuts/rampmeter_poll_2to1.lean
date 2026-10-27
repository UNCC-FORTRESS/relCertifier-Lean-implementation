/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rampmeter_poll_2to1` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rampmeter_poll_2to1`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rampmeter_poll_2to1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rampmeter_poll_2to1_cutsV2 : EvolStrengthening :=
  { L := [
      ("R1800", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict)]),
      ("R1440", [((.cmp ">=" (.var "k") (.num "19")), CutRoute.diStrict), ((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R1200", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R960", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R720", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R480", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)])
    ]
    R := [
      ("R1800", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict)]),
      ("R1440", [((.cmp ">=" (.var "k") (.num "19")), CutRoute.diStrict), ((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R1200", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R960", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R720", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp ">=" (.var "k") (.num "14")), CutRoute.diStrict), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)]),
      ("R480", [((.cmp ">=" (.var "kd") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "kd") (.num "27.5")), CutRoute.frozen), ((.cmp "<=" (.var "k") (.num "42.5")), CutRoute.diStrict)])
    ] }

def rampmeter_poll_2to1_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("R1800", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R1440", [⟨(.cmp ">=" (.var "k") (.num "19")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R1200", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R960", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R720", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "39")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩]),
      ("R480", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("R1800", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R1440", [⟨(.cmp ">=" (.var "k") (.num "19")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R1200", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R960", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("R720", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "k") (.num "14")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "k") (.num "39")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩]),
      ("R480", [⟨(.cmp ">=" (.var "kd") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "kd") (.num "27.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "k") (.num "42.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rampmeter_poll_2to1_cutsV2_wf : evolStrengtheningWF rampmeter_poll_2to1_IRv2 rampmeter_poll_2to1_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rampmeter_poll_2to1_cutsV2X_wf : evolStrengtheningWFX rampmeter_poll_2to1_IRv2 rampmeter_poll_2to1_cutsV2X = true := rfl

end RelCertifier.Oracle

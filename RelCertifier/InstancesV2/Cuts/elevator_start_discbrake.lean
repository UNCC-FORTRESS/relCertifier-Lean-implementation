/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `elevator_start_discbrake` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py elevator_start_discbrake`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.elevator_start_discbrake

namespace RelCertifier.Oracle

open RelCertifier.Parse

def elevator_start_discbrake_cutsV2 : EvolStrengthening :=
  { L := [
      ("LIFT", [((.cmp "<=" (.var "z") (.num "0.1")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.frozen), ((.cmp "<=" (.var "z") (.num "20.5")), CutRoute.frozen), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.frozen), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("UP", [((.cmp ">=" (.var "b") (.num "0.95")), CutRoute.shape), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.shape), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("APP", [((.cmp ">=" (.var "z") (.num "18.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.shape), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("STOP", [((.cmp ">=" (.var "z") (.num "19.9")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.diStrict), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.diStrict)])
    ]
    R := [
      ("LIFT", [((.cmp "<=" (.var "z") (.num "0.1")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.frozen), ((.cmp "<=" (.var "z") (.num "20.5")), CutRoute.frozen), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.frozen), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("UP", [((.cmp ">=" (.var "b") (.num "0.95")), CutRoute.shape), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.shape), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("APP", [((.cmp ">=" (.var "z") (.num "18.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.shape), ((.cmp ">=" (.var "b") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.shape)]),
      ("STOP", [((.cmp ">=" (.var "z") (.num "19.9")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5")), CutRoute.diNonstrict), ((.cmp ">=" (.var "z") (.num "-0.5")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "1.7")), CutRoute.diStrict), ((.cmp "<=" (.var "b") (.num "1.0")), CutRoute.diStrict)])
    ] }

def elevator_start_discbrake_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("LIFT", [⟨(.cmp "<=" (.var "z") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "z") (.num "20.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("UP", [⟨(.cmp ">=" (.var "b") (.num "0.95")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("APP", [⟨(.cmp ">=" (.var "z") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "z") (.num "19.9")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("LIFT", [⟨(.cmp "<=" (.var "z") (.num "0.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "z") (.num "20.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("UP", [⟨(.cmp ">=" (.var "b") (.num "0.95")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("APP", [⟨(.cmp ">=" (.var "z") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "b") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "z") (.num "19.9")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "z") (.bin "*" (.num "0.25") (.var "v"))) (.num "20.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "z") (.num "-0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "b") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem elevator_start_discbrake_cutsV2_wf : evolStrengtheningWF elevator_start_discbrake_IRv2 elevator_start_discbrake_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem elevator_start_discbrake_cutsV2X_wf : evolStrengtheningWFX elevator_start_discbrake_IRv2 elevator_start_discbrake_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `grid_ffr_dos` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py grid_ffr_dos`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.grid_ffr_dos

namespace RelCertifier.Oracle

open RelCertifier.Parse

def grid_ffr_dos_cutsV2 : EvolStrengthening :=
  { L := [
      ("NORMAL", [((.cmp "<=" (.var "a") (.num "0.0")), CutRoute.frozen), ((.cmp ">=" (.var "x") (.num "-2.5")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "d") (.num "0.05")), CutRoute.frozen), ((.cmp "<=" (.var "d") (.num "0.3")), CutRoute.frozen), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "a") (.num "1.0")), CutRoute.frozen)]),
      ("FFR", [((.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "-1.5")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "-2.5")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "d") (.num "0.05")), CutRoute.frozen), ((.cmp "<=" (.var "d") (.num "0.3")), CutRoute.frozen), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "a") (.num "1.0")), CutRoute.shape)])
    ]
    R := [
      ("NORMAL", [((.cmp "<=" (.var "a") (.num "0.0")), CutRoute.frozen), ((.cmp ">=" (.var "x") (.num "-2.5")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "d") (.num "0.05")), CutRoute.frozen), ((.cmp "<=" (.var "d") (.num "0.3")), CutRoute.frozen), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "a") (.num "1.0")), CutRoute.frozen)]),
      ("FFR", [((.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "-1.5")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "-2.5")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "d") (.num "0.05")), CutRoute.frozen), ((.cmp "<=" (.var "d") (.num "0.3")), CutRoute.frozen), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "a") (.num "1.0")), CutRoute.shape)]),
      ("TRIP", [((.cmp "<=" (.var "x") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "d") (.num "0.05")), CutRoute.frozen), ((.cmp "<=" (.var "d") (.num "0.3")), CutRoute.frozen), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "a") (.num "1.0")), CutRoute.frozen)])
    ] }

def grid_ffr_dos_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("NORMAL", [⟨(.cmp "<=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "d") (.num "0.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "d") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "a") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("FFR", [⟨(.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-1.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "d") (.num "0.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "d") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "a") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("NORMAL", [⟨(.cmp "<=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "d") (.num "0.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "d") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "a") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("FFR", [⟨(.cmp "<=" (.bin "-" (.var "x") (.bin "*" (.num "2.0") (.var "a"))) (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-1.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "-2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "d") (.num "0.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "d") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "a") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("TRIP", [⟨(.cmp "<=" (.var "x") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "d") (.num "0.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "d") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "a") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "x") (.num "-1.5")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem grid_ffr_dos_cutsV2_wf : evolStrengtheningWF grid_ffr_dos_IRv2 grid_ffr_dos_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem grid_ffr_dos_cutsV2X_wf : evolStrengtheningWFX grid_ffr_dos_IRv2 grid_ffr_dos_cutsV2X = true := rfl

end RelCertifier.Oracle

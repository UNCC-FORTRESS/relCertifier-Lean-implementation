/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_car_stop` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py drl_car_stop`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.drl_car_stop

namespace RelCertifier.Oracle

open RelCertifier.Parse

def drl_car_stop_cutsV2 : EvolStrengthening :=
  { L := [
      ("Accel", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Coast", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "1.0")), CutRoute.frozen)]),
      ("Brake", [((.cmp "<=" (.var "v") (.num "10.0")), CutRoute.diStrict)])
    ]
    R := [
      ("Accel", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Coast", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "1.0")), CutRoute.frozen)]),
      ("Brake", [((.cmp "<=" (.var "v") (.num "10.0")), CutRoute.diStrict)])
    ] }

def drl_car_stop_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Accel", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Coast", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Brake", [⟨(.cmp "<=" (.var "v") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("Accel", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Coast", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Brake", [⟨(.cmp "<=" (.var "v") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem drl_car_stop_cutsV2_wf : evolStrengtheningWF drl_car_stop_IRv2 drl_car_stop_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem drl_car_stop_cutsV2X_wf : evolStrengtheningWFX drl_car_stop_IRv2 drl_car_stop_cutsV2X = true := rfl

end RelCertifier.Oracle

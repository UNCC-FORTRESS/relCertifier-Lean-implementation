/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `train_ato_odometry` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py train_ato_odometry`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.train_ato_odometry

namespace RelCertifier.Oracle

open RelCertifier.Parse

def train_ato_odometry_cutsV2 : EvolStrengthening :=
  { L := [
      ("PL1", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.var "v") (.num "28.21")), CutRoute.diStrict)]),
      ("PL2", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.var "v") (.num "28.21")), CutRoute.diStrict)]),
      ("PL3", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.var "v") (.num "28.21")), CutRoute.diStrict)])
    ]
    R := [
      ("PL1", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "27.08")), CutRoute.shape)]),
      ("PL2", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "27.08")), CutRoute.shape)]),
      ("PL3", [((.cmp ">=" (.var "v") (.num "5.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "27.08")), CutRoute.shape)])
    ] }

def train_ato_odometry_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("PL1", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "28.21")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("PL2", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "28.21")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("PL3", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "28.21")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("PL1", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "27.08")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("PL2", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "27.08")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("PL3", [⟨(.cmp ">=" (.var "v") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "27.08")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem train_ato_odometry_cutsV2_wf : evolStrengtheningWF train_ato_odometry_IRv2 train_ato_odometry_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem train_ato_odometry_cutsV2X_wf : evolStrengtheningWFX train_ato_odometry_IRv2 train_ato_odometry_cutsV2X = true := rfl

end RelCertifier.Oracle

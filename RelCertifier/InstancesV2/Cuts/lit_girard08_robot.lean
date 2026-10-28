/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_girard08_robot` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_girard08_robot`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.lit_girard08_robot

namespace RelCertifier.Oracle

open RelCertifier.Parse

def lit_girard08_robot_cutsV2 : EvolStrengthening :=
  { L := [
      ("M1", []),
      ("M2", []),
      ("M3", []),
      ("M4", []),
      ("M5", []),
      ("M6", [])
    ]
    R := [
      ("M1", [((.cmp ">=" (.var "wx") (.num "-0.4")), CutRoute.diStrict), ((.cmp ">=" (.var "wy") (.num "-0.4")), CutRoute.frozen)]),
      ("M2", [((.cmp ">=" (.var "wx") (.num "2.6")), CutRoute.diStrict)]),
      ("M3", [((.cmp "<=" (.var "wy") (.num "0.4")), CutRoute.diStrict)]),
      ("M4", [((.cmp "<=" (.var "wx") (.num "0.4")), CutRoute.diStrict), ((.cmp "<=" (.var "wy") (.num "0.4")), CutRoute.frozen)]),
      ("M5", [((.cmp "<=" (.var "wx") (.num "-2.6")), CutRoute.diStrict)]),
      ("M6", [((.cmp ">=" (.var "wy") (.num "-0.4")), CutRoute.diStrict)])
    ] }

def lit_girard08_robot_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("M1", []),
      ("M2", []),
      ("M3", []),
      ("M4", []),
      ("M5", []),
      ("M6", [])
    ]
    R := [
      ("M1", [⟨(.cmp ">=" (.var "wx") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "wy") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("M2", [⟨(.cmp ">=" (.var "wx") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("M3", [⟨(.cmp "<=" (.var "wy") (.num "0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("M4", [⟨(.cmp "<=" (.var "wx") (.num "0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "wy") (.num "0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("M5", [⟨(.cmp "<=" (.var "wx") (.num "-2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("M6", [⟨(.cmp ">=" (.var "wy") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem lit_girard08_robot_cutsV2_wf : evolStrengtheningWF lit_girard08_robot_IRv2 lit_girard08_robot_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem lit_girard08_robot_cutsV2X_wf : evolStrengtheningWFX lit_girard08_robot_IRv2 lit_girard08_robot_cutsV2X = true := rfl

end RelCertifier.Oracle

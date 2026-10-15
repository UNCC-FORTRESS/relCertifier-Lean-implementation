/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_lane_control` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py drl_lane_control`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.drl_lane_control

namespace RelCertifier.Oracle

open RelCertifier.Parse

def drl_lane_control_cutsV2 : EvolStrengthening :=
  { L := [
      ("AccelLAccel", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("AccelLBrake", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)]),
      ("CoastLAccel", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.frozen), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("CoastLBrake", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.frozen), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)]),
      ("BrakeLAccel", [((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("BrakeLBrake", [((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)])
    ]
    R := [
      ("AccelLAccel", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("AccelLBrake", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)]),
      ("CoastLAccel", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.frozen), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("CoastLBrake", [((.cmp ">=" (.var "vf") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.frozen), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)]),
      ("BrakeLAccel", [((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.var "vl") (.num "0.0")), CutRoute.diStrict)]),
      ("BrakeLBrake", [((.cmp "<=" (.var "vf") (.num "10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "vl") (.num "10.0")), CutRoute.diStrict)])
    ] }

def drl_lane_control_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("AccelLAccel", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccelLBrake", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastLAccel", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastLBrake", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BrakeLAccel", [⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BrakeLBrake", [⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("AccelLAccel", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AccelLBrake", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastLAccel", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CoastLBrake", [⟨(.cmp ">=" (.var "vf") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BrakeLAccel", [⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "vl") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("BrakeLBrake", [⟨(.cmp "<=" (.var "vf") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "vl") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem drl_lane_control_cutsV2_wf : evolStrengtheningWF drl_lane_control_IRv2 drl_lane_control_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem drl_lane_control_cutsV2X_wf : evolStrengtheningWFX drl_lane_control_IRv2 drl_lane_control_cutsV2X = true := rfl

end RelCertifier.Oracle

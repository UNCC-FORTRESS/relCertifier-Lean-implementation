/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py vehicle_hypercert`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.vehicle_hypercert

namespace RelCertifier.Oracle

open RelCertifier.Parse

def vehicle_hypercert_cutsV2 : EvolStrengthening :=
  { L := [
      ("Am4", [((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.diStrict)]),
      ("Am2", [((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.diStrict)]),
      ("A0", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.frozen)]),
      ("Ap2", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Ap4", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("Am4", [((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.diStrict)]),
      ("Am2", [((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.diStrict)]),
      ("A0", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.frozen)]),
      ("Ap2", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)]),
      ("Ap4", [((.cmp ">=" (.var "v") (.num "0.0")), CutRoute.diStrict)])
    ] }

def vehicle_hypercert_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Am4", [⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Am2", [⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("A0", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Ap2", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Ap4", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("Am4", [⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Am2", [⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("A0", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("Ap2", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Ap4", [⟨(.cmp ">=" (.var "v") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem vehicle_hypercert_cutsV2_wf : evolStrengtheningWF vehicle_hypercert_IRv2 vehicle_hypercert_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem vehicle_hypercert_cutsV2X_wf : evolStrengtheningWFX vehicle_hypercert_IRv2 vehicle_hypercert_cutsV2X = true := rfl

end RelCertifier.Oracle

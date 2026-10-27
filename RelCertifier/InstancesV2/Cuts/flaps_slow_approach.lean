/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `flaps_slow_approach` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py flaps_slow_approach`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.flaps_slow_approach

namespace RelCertifier.Oracle

open RelCertifier.Parse

def flaps_slow_approach_cutsV2 : EvolStrengthening :=
  { L := [
      ("EXT", [((.cmp ">=" (.var "f") (.num "10")), CutRoute.diStrict), ((.cmp "<=" (.var "V") (.num "185")), CutRoute.diStrict)]),
      ("CONF2", [((.cmp ">=" (.var "f") (.num "15")), CutRoute.frozen), ((.cmp ">=" (.var "f") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "f") (.num "15.1")), CutRoute.frozen), ((.cmp "<=" (.var "V") (.num "185")), CutRoute.diStrict)])
    ]
    R := [
      ("EXT", [((.cmp ">=" (.var "f") (.num "10")), CutRoute.diStrict), ((.cmp "<=" (.var "V") (.num "185")), CutRoute.diStrict)]),
      ("CONF2", [((.cmp ">=" (.var "f") (.num "15")), CutRoute.frozen), ((.cmp ">=" (.var "f") (.num "10")), CutRoute.frozen), ((.cmp "<=" (.var "f") (.num "15.1")), CutRoute.frozen), ((.cmp "<=" (.var "V") (.num "185")), CutRoute.diStrict)])
    ] }

def flaps_slow_approach_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("EXT", [⟨(.cmp ">=" (.var "f") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "V") (.num "185")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CONF2", [⟨(.cmp ">=" (.var "f") (.num "15")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "f") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "f") (.num "15.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "V") (.num "185")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("EXT", [⟨(.cmp ">=" (.var "f") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "V") (.num "185")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("CONF2", [⟨(.cmp ">=" (.var "f") (.num "15")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "f") (.num "10")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "f") (.num "15.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "V") (.num "185")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem flaps_slow_approach_cutsV2_wf : evolStrengtheningWF flaps_slow_approach_IRv2 flaps_slow_approach_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem flaps_slow_approach_cutsV2X_wf : evolStrengtheningWFX flaps_slow_approach_IRv2 flaps_slow_approach_cutsV2X = true := rfl

end RelCertifier.Oracle

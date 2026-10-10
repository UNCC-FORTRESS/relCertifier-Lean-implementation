/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_profiles` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_delay_profiles`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.platoon_delay_profiles

namespace RelCertifier.Oracle

open RelCertifier.Parse

def platoon_delay_profiles_cutsV2 : EvolStrengthening :=
  { L := [
      ("FOLLOW", [((.cmp ">=" (.var "g") (.num "24.0")), CutRoute.diStrict), ((.cmp "<=" (.var "g") (.num "40.0")), CutRoute.diStrict)]),
      ("GENTLE", [])
    ]
    R := [
      ("FOLLOW", [((.cmp ">=" (.var "g") (.num "20.0")), CutRoute.diStrict), ((.cmp "<=" (.var "g") (.num "40.0")), CutRoute.diStrict)]),
      ("GENTLE", []),
      ("ASSERTIVE", []),
      ("BRAKE", [])
    ] }

def platoon_delay_profiles_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("FOLLOW", [⟨(.cmp ">=" (.var "g") (.num "24.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "g") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("GENTLE", [⟨(.cmp ">=" (.var "g") (.num "29.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("FOLLOW", [⟨(.cmp ">=" (.var "g") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "g") (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("GENTLE", [⟨(.cmp ">=" (.var "g") (.num "30.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("ASSERTIVE", [⟨(.cmp ">=" (.var "g") (.num "30.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("BRAKE", [])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem platoon_delay_profiles_cutsV2_wf : evolStrengtheningWF platoon_delay_profiles_IRv2 platoon_delay_profiles_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem platoon_delay_profiles_cutsV2X_wf : evolStrengtheningWFX platoon_delay_profiles_IRv2 platoon_delay_profiles_cutsV2X = true := rfl

end RelCertifier.Oracle

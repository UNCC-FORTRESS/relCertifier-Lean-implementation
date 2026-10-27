/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_profiles` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_profiles`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.platoon_profiles

namespace RelCertifier.Oracle

open RelCertifier.Parse

def platoon_profiles_cutsV2 : EvolStrengthening :=
  { L := [
      ("SPORT", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)]),
      ("AEB", [((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0")), CutRoute.diNonstrict)])
    ]
    R := [
      ("CACC", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)]),
      ("AEB", [((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0")), CutRoute.diNonstrict)])
    ] }

def platoon_profiles_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("SPORT", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AEB", [⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diNonstrict, []⟩])
    ]
    R := [
      ("CACC", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("AEB", [⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diNonstrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem platoon_profiles_cutsV2_wf : evolStrengtheningWF platoon_profiles_IRv2 platoon_profiles_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem platoon_profiles_cutsV2X_wf : evolStrengtheningWFX platoon_profiles_IRv2 platoon_profiles_cutsV2X = true := rfl

end RelCertifier.Oracle

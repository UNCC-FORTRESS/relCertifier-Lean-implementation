/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_linkloss` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_linkloss`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.platoon_linkloss

namespace RelCertifier.Oracle

open RelCertifier.Parse

def platoon_linkloss_cutsV2 : EvolStrengthening :=
  { L := [
      ("CACC", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)]),
      ("ACC", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)])
    ]
    R := [
      ("CACC", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)])
    ] }

def platoon_linkloss_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CACC", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("ACC", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("CACC", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem platoon_linkloss_cutsV2_wf : evolStrengtheningWF platoon_linkloss_IRv2 platoon_linkloss_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem platoon_linkloss_cutsV2X_wf : evolStrengtheningWFX platoon_linkloss_IRv2 platoon_linkloss_cutsV2X = true := rfl

end RelCertifier.Oracle

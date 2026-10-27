/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `antenna_track_kvretune` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py antenna_track_kvretune`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.antenna_track_kvretune

namespace RelCertifier.Oracle

open RelCertifier.Parse

def antenna_track_kvretune_cutsV2 : EvolStrengthening :=
  { L := [
      ("TRACK", [((.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05")), CutRoute.diNonstrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "92.0")), CutRoute.diStrict)]),
      ("STOW", [((.cmp ">=" (.var "t") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "-2.0")), CutRoute.diStrict)]),
      ("STOWED", [((.cmp ">=" (.var "t") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "90.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "-2.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "92.0")), CutRoute.frozen)])
    ]
    R := [
      ("TRACK", [((.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05")), CutRoute.diNonstrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "92.0")), CutRoute.diStrict)]),
      ("STOW", [((.cmp ">=" (.var "t") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "-2.0")), CutRoute.diStrict)]),
      ("STOWED", [((.cmp ">=" (.var "t") (.num "60.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "90.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "-2.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "92.0")), CutRoute.frozen)])
    ] }

def antenna_track_kvretune_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("TRACK", [⟨(.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "92.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("STOW", [⟨(.cmp ">=" (.var "t") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "-2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("STOWED", [⟨(.cmp ">=" (.var "t") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "90.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "-2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "92.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("TRACK", [⟨(.cmp ">=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "46.95")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "c") (.bin "*" (.num "0.7") (.var "t"))) (.num "47.05")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "92.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("STOW", [⟨(.cmp ">=" (.var "t") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "-2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("STOWED", [⟨(.cmp ">=" (.var "t") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "90.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "-2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "92.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem antenna_track_kvretune_cutsV2_wf : evolStrengtheningWF antenna_track_kvretune_IRv2 antenna_track_kvretune_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem antenna_track_kvretune_cutsV2X_wf : evolStrengtheningWFX antenna_track_kvretune_IRv2 antenna_track_kvretune_cutsV2X = true := rfl

end RelCertifier.Oracle

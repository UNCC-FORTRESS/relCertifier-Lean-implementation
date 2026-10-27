/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bottling_fill_strainer` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bottling_fill_strainer`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.bottling_fill_strainer

namespace RelCertifier.Oracle

open RelCertifier.Parse

def bottling_fill_strainer_cutsV2 : EvolStrengthening :=
  { L := [
      ("FILL", [((.cmp ">=" (.var "u") (.num "1.0")), CutRoute.frozen), ((.cmp ">=" (.var "V") (.num "0.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "u") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "u") (.num "1.0")), CutRoute.frozen)]),
      ("CLOSE", [((.cmp ">=" (.var "V") (.num "994.0")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "6.8") (.var "u"))) (.num "1060.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "V") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "1.0")), CutRoute.diStrict)])
    ]
    R := [
      ("FILL", [((.cmp ">=" (.var "u") (.num "1.0")), CutRoute.frozen), ((.cmp ">=" (.var "V") (.num "0.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "u") (.num "0.0")), CutRoute.frozen), ((.cmp "<=" (.var "u") (.num "1.0")), CutRoute.frozen)]),
      ("CLOSE", [((.cmp ">=" (.var "V") (.num "994.0")), CutRoute.diNonstrict), ((.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "8.0") (.var "u"))) (.num "1060.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "V") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "u") (.num "1.0")), CutRoute.diStrict)])
    ] }

def bottling_fill_strainer_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("FILL", [⟨(.cmp ">=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "V") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CLOSE", [⟨(.cmp ">=" (.var "V") (.num "994.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "6.8") (.var "u"))) (.num "1060.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("FILL", [⟨(.cmp ">=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "V") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("CLOSE", [⟨(.cmp ">=" (.var "V") (.num "994.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "V") (.bin "*" (.num "8.0") (.var "u"))) (.num "1060.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem bottling_fill_strainer_cutsV2_wf : evolStrengtheningWF bottling_fill_strainer_IRv2 bottling_fill_strainer_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem bottling_fill_strainer_cutsV2X_wf : evolStrengtheningWFX bottling_fill_strainer_IRv2 bottling_fill_strainer_cutsV2X = true := rfl

end RelCertifier.Oracle

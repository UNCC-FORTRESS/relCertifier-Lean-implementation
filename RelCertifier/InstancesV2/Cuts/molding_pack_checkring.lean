/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `molding_pack_checkring` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py molding_pack_checkring`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.molding_pack_checkring

namespace RelCertifier.Oracle

open RelCertifier.Parse

def molding_pack_checkring_cutsV2 : EvolStrengthening :=
  { L := [
      ("HOLD", [((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "2000.0")), CutRoute.diStrict)]),
      ("COOL", [((.cmp ">=" (.var "t") (.num "5.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "2000.0")), CutRoute.diStrict), ((.cmp "<=" (.var "y") (.num "2000.0")), CutRoute.diStrict)])
    ]
    R := [
      ("HOLD", [((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "2000.0")), CutRoute.diStrict)]),
      ("COOL", [((.cmp ">=" (.var "t") (.num "5.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "x") (.num "2000.0")), CutRoute.diStrict), ((.cmp "<=" (.var "y") (.num "2000.0")), CutRoute.diStrict)])
    ] }

def molding_pack_checkring_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("HOLD", [⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("COOL", [⟨(.cmp ">=" (.var "t") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "y") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("HOLD", [⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "x") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("COOL", [⟨(.cmp ">=" (.var "t") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "x") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "y") (.num "2000.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem molding_pack_checkring_cutsV2_wf : evolStrengtheningWF molding_pack_checkring_IRv2 molding_pack_checkring_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem molding_pack_checkring_cutsV2X_wf : evolStrengtheningWFX molding_pack_checkring_IRv2 molding_pack_checkring_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bms_chiller_undercharge` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bms_chiller_undercharge`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.bms_chiller_undercharge

namespace RelCertifier.Oracle

open RelCertifier.Parse

def bms_chiller_undercharge_cutsV2 : EvolStrengthening :=
  { L := [
      ("COAST", [((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.shape)]),
      ("CHILL", [((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.shape)])
    ]
    R := [
      ("COAST", [((.cmp ">=" (.var "T") (.num "0.0")), CutRoute.shape)]),
      ("CHILL_LO", [((.cmp ">=" (.var "T") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.shape)]),
      ("CHILL_HI", [((.cmp ">=" (.var "T") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "T") (.num "60.0")), CutRoute.shape)])
    ] }

def bms_chiller_undercharge_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("COAST", [⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "50")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("CHILL", [⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "T") (.num "27")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("COAST", [⟨(.cmp ">=" (.var "T") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "50")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("CHILL_LO", [⟨(.cmp ">=" (.var "T") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("CHILL_HI", [⟨(.cmp ">=" (.var "T") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "T") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem bms_chiller_undercharge_cutsV2_wf : evolStrengtheningWF bms_chiller_undercharge_IRv2 bms_chiller_undercharge_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem bms_chiller_undercharge_cutsV2X_wf : evolStrengtheningWFX bms_chiller_undercharge_IRv2 bms_chiller_undercharge_cutsV2X = true := rfl

end RelCertifier.Oracle

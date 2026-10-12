/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank_twospeed`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.watertank_twospeed

namespace RelCertifier.Oracle

open RelCertifier.Parse

def watertank_twospeed_cutsV2 : EvolStrengthening :=
  { L := [
      ("Low", [((.cmp ">=" (.var "x") (.num "5.0")), CutRoute.shape)])
    ]
    R := [
      ("Fast", [((.cmp ">=" (.var "x") (.num "2.0")), CutRoute.shape)]),
      ("Slow", [((.cmp ">=" (.var "x") (.num "8.0")), CutRoute.shape)])
    ] }

def watertank_twospeed_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Low", [⟨(.cmp ">=" (.var "x") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "15.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("Fast", [⟨(.cmp ">=" (.var "x") (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "12.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("Slow", [⟨(.cmp ">=" (.var "x") (.num "8.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem watertank_twospeed_cutsV2_wf : evolStrengtheningWF watertank_twospeed_IRv2 watertank_twospeed_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem watertank_twospeed_cutsV2X_wf : evolStrengtheningWFX watertank_twospeed_IRv2 watertank_twospeed_cutsV2X = true := rfl

end RelCertifier.Oracle

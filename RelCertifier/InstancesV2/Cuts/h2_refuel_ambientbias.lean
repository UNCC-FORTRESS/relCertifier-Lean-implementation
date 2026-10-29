/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py h2_refuel_ambientbias`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.h2_refuel_ambientbias

namespace RelCertifier.Oracle

open RelCertifier.Parse

def h2_refuel_ambientbias_cutsV2 : EvolStrengthening :=
  { L := [
      ("STAGE1", []),
      ("STAGE2", [((.cmp ">=" (.var "p") (.num "18.0")), CutRoute.shape)]),
      ("STAGE3", [((.cmp ">=" (.var "p") (.num "38.0")), CutRoute.shape)]),
      ("TOPOFF", [((.cmp ">=" (.var "p") (.num "58.0")), CutRoute.shape)]),
      ("COMPLETE", [((.cmp ">=" (.var "p") (.num "72.4")), CutRoute.frozen)])
    ]
    R := [
      ("STAGE1", []),
      ("STAGE2", [((.cmp ">=" (.var "p") (.num "18.0")), CutRoute.shape)]),
      ("STAGE3", [((.cmp ">=" (.var "p") (.num "38.0")), CutRoute.shape)]),
      ("TOPOFF", [((.cmp ">=" (.var "p") (.num "58.0")), CutRoute.shape)]),
      ("COMPLETE", [((.cmp ">=" (.var "p") (.num "70.0")), CutRoute.frozen)])
    ] }

def h2_refuel_ambientbias_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STAGE1", [⟨(.cmp "<=" (.var "p") (.num "20")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STAGE2", [⟨(.cmp ">=" (.var "p") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "40")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STAGE3", [⟨(.cmp ">=" (.var "p") (.num "38.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "60")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("TOPOFF", [⟨(.cmp ">=" (.var "p") (.num "58.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "72.9")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("COMPLETE", [⟨(.cmp ">=" (.var "p") (.num "72.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("STAGE1", [⟨(.cmp "<=" (.var "p") (.num "20")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STAGE2", [⟨(.cmp ">=" (.var "p") (.num "18.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "40")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STAGE3", [⟨(.cmp ">=" (.var "p") (.num "38.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "60")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("TOPOFF", [⟨(.cmp ">=" (.var "p") (.num "58.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "70.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("COMPLETE", [⟨(.cmp ">=" (.var "p") (.num "70.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem h2_refuel_ambientbias_cutsV2_wf : evolStrengtheningWF h2_refuel_ambientbias_IRv2 h2_refuel_ambientbias_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem h2_refuel_ambientbias_cutsV2X_wf : evolStrengtheningWFX h2_refuel_ambientbias_IRv2 h2_refuel_ambientbias_cutsV2X = true := rfl

end RelCertifier.Oracle

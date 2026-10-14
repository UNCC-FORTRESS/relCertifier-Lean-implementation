/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_choice` (choice exhibit) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.Choice.BenchIR.watertank_choice

namespace RelCertifier.Oracle

open RelCertifier.Parse

def watertank_choice_cutsC : EvolStrengthening :=
  { L := [
      ("Low", [((.cmp ">=" (.var "x") (.num "5.0")), CutRoute.shape)]),
      ("Mid", [((.cmp ">=" (.var "x") (.num "13.0")), CutRoute.shape)]),
      ("High", [((.cmp ">=" (.var "x") (.num "20.0")), CutRoute.shape)])
    ]
    R := [
      ("Low", [((.cmp ">=" (.var "x") (.num "2.0")), CutRoute.shape)]),
      ("MidEco", [((.cmp ">=" (.var "x") (.num "10.0")), CutRoute.shape)]),
      ("MidBoost", [((.cmp ">=" (.var "x") (.num "10.0")), CutRoute.shape)]),
      ("High", [((.cmp ">=" (.var "x") (.num "17.0")), CutRoute.shape)]),
      ("PumpOff", [])
    ] }

def watertank_choice_cutsCX : EvolStrengtheningX :=
  { L := [
      ("Low", [⟨(.cmp ">=" (.var "x") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "15.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("Mid", [⟨(.cmp ">=" (.var "x") (.num "13.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "20.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("High", [⟨(.cmp ">=" (.var "x") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("Low", [⟨(.cmp ">=" (.var "x") (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "12.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("MidEco", [⟨(.cmp ">=" (.var "x") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "17.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("MidBoost", [⟨(.cmp ">=" (.var "x") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "x") (.num "17.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("High", [⟨(.cmp ">=" (.var "x") (.num "17.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("PumpOff", [⟨(.cmp "<=" (.var "x") (.num "2.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem watertank_choice_cutsC_wf : evolStrengtheningWF watertank_choice_IRc watertank_choice_cutsC = true := rfl

/-- The extended certificate is well formed. -/
theorem watertank_choice_cutsCX_wf : evolStrengtheningWFX watertank_choice_IRc watertank_choice_cutsCX = true := rfl

end RelCertifier.Oracle

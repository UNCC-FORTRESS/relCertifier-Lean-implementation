/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_start_highidle` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py engine_start_highidle`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.engine_start_highidle

namespace RelCertifier.Oracle

open RelCertifier.Parse

def engine_start_highidle_cutsV2 : EvolStrengthening :=
  { L := [
      ("STARTER", [((.cmp ">=" (.var "n") (.num "5.0")), CutRoute.shape), ((.cmp ">=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("STARTER_LOW", [((.cmp ">=" (.var "n") (.num "5.0")), CutRoute.shape)]),
      ("LIGHTOFF", [((.cmp ">=" (.var "n") (.num "25.0")), CutRoute.shape)]),
      ("SELF", [((.cmp ">=" (.var "n") (.num "50.0")), CutRoute.shape)]),
      ("IDLE", [((.cmp ">=" (.var "n") (.num "60.0")), CutRoute.shape)]),
      ("ABORT", [((.cmp ">=" (.var "t") (.num "30.0")), CutRoute.frozen)])
    ]
    R := [
      ("STARTER", [((.cmp ">=" (.var "n") (.num "5.0")), CutRoute.shape), ((.cmp ">=" (.var "p") (.num "35.0")), CutRoute.frozen)]),
      ("STARTER_LOW", [((.cmp ">=" (.var "n") (.num "5.0")), CutRoute.shape)]),
      ("LIGHTOFF", [((.cmp ">=" (.var "n") (.num "25.0")), CutRoute.shape)]),
      ("SELF", [((.cmp ">=" (.var "n") (.num "50.0")), CutRoute.shape)]),
      ("IDLE", [((.cmp ">=" (.var "n") (.num "60.0")), CutRoute.shape)]),
      ("ABORT", [((.cmp ">=" (.var "t") (.num "30.0")), CutRoute.frozen)])
    ] }

def engine_start_highidle_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STARTER", [⟨(.cmp ">=" (.var "n") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "30")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STARTER_LOW", [⟨(.cmp ">=" (.var "n") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "25.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("LIGHTOFF", [⟨(.cmp ">=" (.var "n") (.num "25.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "n") (.num "55")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("SELF", [⟨(.cmp ">=" (.var "n") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "n") (.num "66")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("IDLE", [⟨(.cmp ">=" (.var "n") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("ABORT", [⟨(.cmp ">=" (.var "t") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "25.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("STARTER", [⟨(.cmp ">=" (.var "n") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "p") (.num "35.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "30")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("STARTER_LOW", [⟨(.cmp ">=" (.var "n") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "p") (.num "35.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "25.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("LIGHTOFF", [⟨(.cmp ">=" (.var "n") (.num "25.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "n") (.num "55")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("SELF", [⟨(.cmp ">=" (.var "n") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "n") (.num "62")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("IDLE", [⟨(.cmp ">=" (.var "n") (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("ABORT", [⟨(.cmp ">=" (.var "t") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "n") (.num "25.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem engine_start_highidle_cutsV2_wf : evolStrengtheningWF engine_start_highidle_IRv2 engine_start_highidle_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem engine_start_highidle_cutsV2X_wf : evolStrengtheningWFX engine_start_highidle_IRv2 engine_start_highidle_cutsV2X = true := rfl

end RelCertifier.Oracle

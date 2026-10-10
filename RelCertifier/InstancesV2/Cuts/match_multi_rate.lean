/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py match_multi_rate`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.match_multi_rate

namespace RelCertifier.Oracle

open RelCertifier.Parse

def match_multi_rate_cutsV2 : EvolStrengthening :=
  { L := [
      ("FAST", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape)]),
      ("MEDIUM", [((.cmp ">=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("SLOW", [((.cmp ">=" (.var "v") (.num "0.7")), CutRoute.shape)]),
      ("RESET", [])
    ]
    R := [
      ("DRIVE", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.0")), CutRoute.shape)]),
      ("STALL", [])
    ] }

def match_multi_rate_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("FAST", [⟨(.cmp ">=" (.var "v") (.num "0.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("MEDIUM", [⟨(.cmp ">=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("SLOW", [⟨(.cmp ">=" (.var "v") (.num "0.7")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("RESET", [⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.1")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("DRIVE", [⟨(.cmp ">=" (.var "v") (.num "0.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("STALL", [⟨(.cmp "<=" (.var "v") (.num "0.2")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem match_multi_rate_cutsV2_wf : evolStrengtheningWF match_multi_rate_IRv2 match_multi_rate_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem match_multi_rate_cutsV2X_wf : evolStrengtheningWFX match_multi_rate_IRv2 match_multi_rate_cutsV2X = true := rfl

end RelCertifier.Oracle

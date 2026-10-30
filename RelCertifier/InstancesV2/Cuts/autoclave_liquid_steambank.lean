/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `autoclave_liquid_steambank` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py autoclave_liquid_steambank`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.autoclave_liquid_steambank

namespace RelCertifier.Oracle

open RelCertifier.Parse

def autoclave_liquid_steambank_cutsV2 : EvolStrengthening :=
  { L := [
      ("HEAT", [((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)]),
      ("EQUIL", [((.cmp ">=" (.var "c") (.num "122.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "124.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)]),
      ("EXPOSE", [((.cmp ">=" (.var "c") (.num "122.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "124.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict)]),
      ("EXHAUST", [((.cmp ">=" (.var "t") (.num "15.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.shape), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)])
    ]
    R := [
      ("HEAT", [((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)]),
      ("EQUIL", [((.cmp ">=" (.var "c") (.num "122.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "124.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)]),
      ("EXPOSE", [((.cmp ">=" (.var "c") (.num "122.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "124.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.frozen), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict)]),
      ("EXHAUST", [((.cmp ">=" (.var "t") (.num "15.0")), CutRoute.frozen), ((.cmp ">=" (.var "c") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "c") (.num "138.0")), CutRoute.shape), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.frozen)])
    ] }

def autoclave_liquid_steambank_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("HEAT", [⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "t") (.num "15.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩]),
      ("EQUIL", [⟨(.cmp ">=" (.var "c") (.num "122.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "124.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "t") (.num "15.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩]),
      ("EXPOSE", [⟨(.cmp ">=" (.var "c") (.num "122.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "124.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("EXHAUST", [⟨(.cmp ">=" (.var "t") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("HEAT", [⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "t") (.num "15.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩]),
      ("EQUIL", [⟨(.cmp ">=" (.var "c") (.num "122.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "124.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "t") (.num "15.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩]),
      ("EXPOSE", [⟨(.cmp ">=" (.var "c") (.num "122.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "124.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("EXHAUST", [⟨(.cmp ">=" (.var "t") (.num "15.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "c") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "c") (.num "138.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem autoclave_liquid_steambank_cutsV2_wf : evolStrengtheningWF autoclave_liquid_steambank_IRv2 autoclave_liquid_steambank_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem autoclave_liquid_steambank_cutsV2X_wf : evolStrengtheningWFX autoclave_liquid_steambank_IRv2 autoclave_liquid_steambank_cutsV2X = true := rfl

end RelCertifier.Oracle

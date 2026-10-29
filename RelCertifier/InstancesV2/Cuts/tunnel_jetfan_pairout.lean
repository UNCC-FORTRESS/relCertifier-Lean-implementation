/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tunnel_jetfan_pairout` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tunnel_jetfan_pairout`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.tunnel_jetfan_pairout

namespace RelCertifier.Oracle

open RelCertifier.Parse

def tunnel_jetfan_pairout_cutsV2 : EvolStrengthening :=
  { L := [
      ("NORMAL", [((.cmp "<=" (.var "c") (.num "100")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0")), CutRoute.diStrict), ((.cmp ">=" (.var "u") (.num "2.6")), CutRoute.diStrict), ((.cmp "<=" (.var "u") (.num "7.3")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "900")), CutRoute.diStrict)]),
      ("FIRE", [((.cmp ">=" (.var "t") (.num "600")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0")), CutRoute.diStrict), ((.cmp ">=" (.var "u") (.num "2.6")), CutRoute.diStrict), ((.cmp "<=" (.var "u") (.num "7.3")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "900")), CutRoute.diStrict)])
    ]
    R := [
      ("NORMAL", [((.cmp "<=" (.var "c") (.num "100")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0")), CutRoute.diStrict), ((.cmp ">=" (.var "u") (.num "2.6")), CutRoute.diStrict), ((.cmp "<=" (.var "u") (.num "7.3")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "900")), CutRoute.diStrict)]),
      ("FIRE", [((.cmp ">=" (.var "t") (.num "600")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0")), CutRoute.diStrict), ((.cmp ">=" (.var "u") (.num "2.6")), CutRoute.diStrict), ((.cmp "<=" (.var "u") (.num "7.3")), CutRoute.diStrict), ((.cmp ">=" (.var "c") (.num "0")), CutRoute.diStrict), ((.cmp "<=" (.var "c") (.num "900")), CutRoute.diStrict)])
    ] }

def tunnel_jetfan_pairout_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("NORMAL", [⟨(.cmp "<=" (.var "c") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "7.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "900")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("FIRE", [⟨(.cmp ">=" (.var "t") (.num "600")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "7.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "900")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("NORMAL", [⟨(.cmp "<=" (.var "c") (.num "100")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "7.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "900")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("FIRE", [⟨(.cmp ">=" (.var "t") (.num "600")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "u") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "u") (.num "7.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "c") (.num "0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "c") (.num "900")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem tunnel_jetfan_pairout_cutsV2_wf : evolStrengtheningWF tunnel_jetfan_pairout_IRv2 tunnel_jetfan_pairout_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem tunnel_jetfan_pairout_cutsV2X_wf : evolStrengtheningWFX tunnel_jetfan_pairout_IRv2 tunnel_jetfan_pairout_cutsV2X = true := rfl

end RelCertifier.Oracle

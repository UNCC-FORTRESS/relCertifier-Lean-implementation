/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_latency` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_latency`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.platoon_latency

namespace RelCertifier.Oracle

open RelCertifier.Parse

def platoon_latency_cutsV2 : EvolStrengthening :=
  { L := [
      ("CACC_UP", []),
      ("CACC_DN", [])
    ]
    R := [
      ("CACC", [((.cmp ">=" (.var "r") (.num "-10.0")), CutRoute.diStrict), ((.cmp "<=" (.var "r") (.num "10.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutRoute.diStrict)])
    ] }

def platoon_latency_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CACC_UP", []),
      ("CACC_DN", [])
    ]
    R := [
      ("CACC", [⟨(.cmp ">=" (.var "r") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "r") (.num "10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "g") (.bin "*" (.num "2.0") (.var "r"))) (.num "60.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem platoon_latency_cutsV2_wf : evolStrengtheningWF platoon_latency_IRv2 platoon_latency_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem platoon_latency_cutsV2X_wf : evolStrengtheningWFX platoon_latency_IRv2 platoon_latency_cutsV2X = true := rfl

end RelCertifier.Oracle

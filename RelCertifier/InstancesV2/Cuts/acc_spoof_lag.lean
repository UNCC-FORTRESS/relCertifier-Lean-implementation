/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_lag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_spoof_lag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.acc_spoof_lag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def acc_spoof_lag_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [])
    ]
    R := [
      ("CRUISE", [((.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "40.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "66.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "44.0")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "62.0")), CutRoute.diStrict)])
    ] }

def acc_spoof_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [])
    ]
    R := [
      ("CRUISE", [⟨(.cmp ">=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "40.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.bin "*" (.num "3.0") (.var "a")) (.bin "*" (.num "2.0") (.var "v"))) (.num "66.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "44.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.0") (.var "v"))) (.num "62.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem acc_spoof_lag_cutsV2_wf : evolStrengtheningWF acc_spoof_lag_IRv2 acc_spoof_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem acc_spoof_lag_cutsV2X_wf : evolStrengtheningWFX acc_spoof_lag_IRv2 acc_spoof_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

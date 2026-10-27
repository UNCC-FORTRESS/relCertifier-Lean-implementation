/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_tune_lag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def acc_tune_lag_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1.25") (.bin "-" (.var "v") (.num "30.0")))) (.neg (.num "8.25"))), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1.25") (.bin "-" (.var "v") (.num "30.0")))) (.num "2.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1.875") (.bin "-" (.var "v") (.num "30.0")))) (.neg (.num "11.375"))), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1.875") (.bin "-" (.var "v") (.num "30.0")))) (.num "2.0")), CutRoute.diStrict)])
    ]
    R := [
      ("CRUISE", [((.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.var "v"))) (.num "60.5")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.var "v"))) (.num "77.0")), CutRoute.diStrict), ((.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "0.625") (.var "v"))) (.num "13.625")), CutRoute.diStrict), ((.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "0.625") (.var "v"))) (.num "20.75")), CutRoute.diStrict)])
    ] }

def acc_tune_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1.25") (.bin "-" (.var "v") (.num "30.0")))) (.neg (.num "8.25"))), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1.25") (.bin "-" (.var "v") (.num "30.0")))) (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1.875") (.bin "-" (.var "v") (.num "30.0")))) (.neg (.num "11.375"))), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1.875") (.bin "-" (.var "v") (.num "30.0")))) (.num "2.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("CRUISE", [⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.var "v"))) (.num "60.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.var "v"))) (.num "77.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "0.625") (.var "v"))) (.num "13.625")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "0.625") (.var "v"))) (.num "20.75")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem acc_tune_lag_cutsV2_wf : evolStrengtheningWF acc_tune_lag_IRv2 acc_tune_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem acc_tune_lag_cutsV2X_wf : evolStrengtheningWFX acc_tune_lag_IRv2 acc_tune_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

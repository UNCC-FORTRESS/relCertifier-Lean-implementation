/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_lag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.quad_light_lag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def quad_light_lag_cutsV2 : EvolStrengthening :=
  { L := [
      ("CLIMB", [((.cmp "<=" (.var "w") (.num "2.5")), CutRoute.diStrict), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "a") (.num "7.45")), CutRoute.shape)])
    ]
    R := [
      ("CLIMB", [((.cmp ">=" (.var "w") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "w") (.num "2.6")), CutRoute.diStrict)])
    ] }

def quad_light_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CLIMB", [⟨(.cmp "<=" (.var "w") (.num "2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "a") (.num "7.45")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("CLIMB", [⟨(.cmp ">=" (.var "w") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "2.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem quad_light_lag_cutsV2_wf : evolStrengtheningWF quad_light_lag_IRv2 quad_light_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem quad_light_lag_cutsV2X_wf : evolStrengtheningWFX quad_light_lag_IRv2 quad_light_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

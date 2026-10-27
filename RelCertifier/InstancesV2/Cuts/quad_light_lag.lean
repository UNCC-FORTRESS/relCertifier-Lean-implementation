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
      ("CLIMB", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "a") (.num "14.715")), CutRoute.shape)])
    ]
    R := [
      ("CLIMB", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "a") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "a") (.num "9.81")), CutRoute.shape)])
    ] }

def quad_light_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CLIMB", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "a") (.num "14.715")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("CLIMB", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "a") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "a") (.num "9.81")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem quad_light_lag_cutsV2_wf : evolStrengtheningWF quad_light_lag_IRv2 quad_light_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem quad_light_lag_cutsV2X_wf : evolStrengtheningWFX quad_light_lag_IRv2 quad_light_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

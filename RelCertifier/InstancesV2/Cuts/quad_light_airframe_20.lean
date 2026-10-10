/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_airframe_20`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.quad_light_airframe_20

namespace RelCertifier.Oracle

open RelCertifier.Parse

def quad_light_airframe_20_cutsV2 : EvolStrengthening :=
  { L := [
      ("CLIMB", [((.cmp ">=" (.var "w") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "w") (.num "2.5")), CutRoute.diStrict)])
    ]
    R := [
      ("CLIMB", [((.cmp ">=" (.var "w") (.num "0.0")), CutRoute.diStrict), ((.cmp "<=" (.var "w") (.num "3.0")), CutRoute.diStrict)]),
      ("LIMIT", [])
    ] }

def quad_light_airframe_20_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CLIMB", [⟨(.cmp ">=" (.var "w") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "2.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("CLIMB", [⟨(.cmp ">=" (.var "w") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "3.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("LIMIT", [⟨(.cmp ">=" (.var "w") (.num "0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem quad_light_airframe_20_cutsV2_wf : evolStrengtheningWF quad_light_airframe_20_IRv2 quad_light_airframe_20_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem quad_light_airframe_20_cutsV2X_wf : evolStrengtheningWFX quad_light_airframe_20_IRv2 quad_light_airframe_20_cutsV2X = true := rfl

end RelCertifier.Oracle

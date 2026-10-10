/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover3tier_rung12`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover3tier_rung12

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover3tier_rung12_cutsV2 : EvolStrengthening :=
  { L := [
      ("ACCEL", []),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diStrict)]),
      ("COAST", [((.cmp ">=" (.var "v") (.num "0.6")), CutRoute.diStrict)])
    ] }

def rover3tier_rung12_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("ACCEL", []),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [⟨(.cmp ">=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("COAST", [⟨(.cmp ">=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover3tier_rung12_cutsV2_wf : evolStrengtheningWF rover3tier_rung12_IRv2 rover3tier_rung12_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover3tier_rung12_cutsV2X_wf : evolStrengtheningWFX rover3tier_rung12_IRv2 rover3tier_rung12_cutsV2X = true := rfl

end RelCertifier.Oracle

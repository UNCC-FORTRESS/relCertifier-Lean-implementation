/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_spoof_limp` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_spoof_limp`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.acc_spoof_limp

namespace RelCertifier.Oracle

open RelCertifier.Parse

def acc_spoof_limp_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.diStrict)]),
      ("LIMP", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "30.0")), CutRoute.shape)])
    ]
    R := [
      ("NORMAL", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.shape)]),
      ("ECO", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.shape)]),
      ("SPORT", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.shape)]),
      ("DISENGAGE", [])
    ] }

def acc_spoof_limp_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "40.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩]),
      ("LIMP", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "30.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ]
    R := [
      ("NORMAL", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "40.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("ECO", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "40.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("SPORT", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "40.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("DISENGAGE", [⟨(.cmp "<=" (.var "v") (.num "20.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem acc_spoof_limp_cutsV2_wf : evolStrengtheningWF acc_spoof_limp_IRv2 acc_spoof_limp_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem acc_spoof_limp_cutsV2X_wf : evolStrengtheningWFX acc_spoof_limp_IRv2 acc_spoof_limp_cutsV2X = true := rfl

end RelCertifier.Oracle

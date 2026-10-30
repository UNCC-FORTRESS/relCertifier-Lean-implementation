/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py turbine_startup_gearratio`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.turbine_startup_gearratio

namespace RelCertifier.Oracle

open RelCertifier.Parse

def turbine_startup_gearratio_cutsV2 : EvolStrengthening :=
  { L := [
      ("SPINUP", [((.cmp ">=" (.var "w") (.num "2.1")), CutRoute.shape)]),
      ("RAMP", [((.cmp ">=" (.var "w") (.num "5.25")), CutRoute.shape)]),
      ("GEN", [((.cmp ">=" (.var "w") (.num "7.245")), CutRoute.shape)]),
      ("REG", [((.cmp ">=" (.var "w") (.num "12.57795")), CutRoute.shape)]),
      ("GUST", [((.cmp ">=" (.var "w") (.num "12.57795")), CutRoute.diStrict)])
    ]
    R := [
      ("SPINUP", [((.cmp ">=" (.var "w") (.num "2")), CutRoute.shape)]),
      ("RAMP", [((.cmp ">=" (.var "w") (.num "5")), CutRoute.shape)]),
      ("GEN", [((.cmp ">=" (.var "w") (.num "6.9")), CutRoute.shape)]),
      ("REG", [((.cmp ">=" (.var "w") (.num "11.979")), CutRoute.shape)]),
      ("GUST", [((.cmp ">=" (.var "w") (.num "11.979")), CutRoute.diStrict)])
    ] }

def turbine_startup_gearratio_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("SPINUP", [⟨(.cmp ">=" (.var "w") (.num "2.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "9")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("RAMP", [⟨(.cmp ">=" (.var "w") (.num "5.25")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "7.875")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("GEN", [⟨(.cmp ">=" (.var "w") (.num "7.245")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "12.705")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("REG", [⟨(.cmp ">=" (.var "w") (.num "12.57795")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("GUST", [⟨(.cmp ">=" (.var "w") (.num "12.57795")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("SPINUP", [⟨(.cmp ">=" (.var "w") (.num "2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "9")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("RAMP", [⟨(.cmp ">=" (.var "w") (.num "5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "7.5")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("GEN", [⟨(.cmp ">=" (.var "w") (.num "6.9")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "w") (.num "12.1")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("REG", [⟨(.cmp ">=" (.var "w") (.num "11.979")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("GUST", [⟨(.cmp ">=" (.var "w") (.num "11.979")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem turbine_startup_gearratio_cutsV2_wf : evolStrengtheningWF turbine_startup_gearratio_IRv2 turbine_startup_gearratio_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem turbine_startup_gearratio_cutsV2X_wf : evolStrengtheningWFX turbine_startup_gearratio_IRv2 turbine_startup_gearratio_cutsV2X = true := rfl

end RelCertifier.Oracle

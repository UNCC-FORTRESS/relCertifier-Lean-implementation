/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_nahs25_salt_tank` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_nahs25_salt_tank`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.lit_nahs25_salt_tank

namespace RelCertifier.Oracle

open RelCertifier.Parse

def lit_nahs25_salt_tank_cutsV2 : EvolStrengthening :=
  { L := [
      ("On", [((.cmp ">=" (.var "xp") (.num "22.0")), CutRoute.shape)]),
      ("Off", [])
    ]
    R := [
      ("On", [((.cmp ">=" (.var "xp") (.num "25.0")), CutRoute.shape)]),
      ("Off", [])
    ] }

def lit_nahs25_salt_tank_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("On", [⟨(.cmp ">=" (.var "xp") (.num "22.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("Off", [⟨(.cmp "<=" (.var "xp") (.num "28.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("On", [⟨(.cmp ">=" (.var "xp") (.num "25.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("Off", [⟨(.cmp "<=" (.var "xp") (.num "25.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem lit_nahs25_salt_tank_cutsV2_wf : evolStrengtheningWF lit_nahs25_salt_tank_IRv2 lit_nahs25_salt_tank_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem lit_nahs25_salt_tank_cutsV2X_wf : evolStrengtheningWFX lit_nahs25_salt_tank_IRv2 lit_nahs25_salt_tank_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf25_salt_tank_hold` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_csf25_salt_tank_hold`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.lit_csf25_salt_tank_hold

namespace RelCertifier.Oracle

open RelCertifier.Parse

def lit_csf25_salt_tank_hold_cutsV2 : EvolStrengthening :=
  { L := [
      ("HoldInc", [((.cmp ">=" (.var "t") (.num "5.0")), CutRoute.diStrict)]),
      ("HoldDec", [((.cmp ">=" (.var "t") (.num "5.0")), CutRoute.diStrict)])
    ]
    R := [
      ("Inc", []),
      ("Dec", [])
    ] }

def lit_csf25_salt_tank_hold_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("HoldInc", [⟨(.cmp ">=" (.var "t") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "xp") (.num "100.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("HoldDec", [⟨(.cmp ">=" (.var "t") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "xp") (.num "25.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("Inc", [⟨(.cmp "<=" (.var "xp") (.num "100.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("Dec", [⟨(.cmp ">=" (.var "xp") (.num "25.0")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem lit_csf25_salt_tank_hold_cutsV2_wf : evolStrengtheningWF lit_csf25_salt_tank_hold_IRv2 lit_csf25_salt_tank_hold_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem lit_csf25_salt_tank_hold_cutsV2X_wf : evolStrengtheningWFX lit_csf25_salt_tank_hold_IRv2 lit_csf25_salt_tank_hold_cutsV2X = true := rfl

end RelCertifier.Oracle

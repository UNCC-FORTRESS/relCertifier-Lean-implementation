/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hold_reposition_strict` (prelanding_demo) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.hold_reposition_strict

namespace RelCertifier.Oracle

open RelCertifier.Parse

def hold_reposition_strict_cutsV2 : EvolStrengthening :=
  { L := [
      ("Hold", [((.cmp ">=" (.var "y") (.num "-10.0")), CutRoute.frozen)])
    ]
    R := [
      ("Up", []),
      ("Hold", [((.cmp ">=" (.var "y") (.num "0.0")), CutRoute.frozen)])
    ] }

def hold_reposition_strict_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Hold", [⟨(.cmp ">=" (.var "y") (.num "-10.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("Up", []),
      ("Hold", [⟨(.cmp ">=" (.var "y") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem hold_reposition_strict_cutsV2_wf : evolStrengtheningWF hold_reposition_strict_IRv2 hold_reposition_strict_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem hold_reposition_strict_cutsV2X_wf : evolStrengtheningWFX hold_reposition_strict_IRv2 hold_reposition_strict_cutsV2X = true := rfl

end RelCertifier.Oracle

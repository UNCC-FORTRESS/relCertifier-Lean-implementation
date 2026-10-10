/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_crit` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py arm_plateau_crit`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.arm_plateau_crit

namespace RelCertifier.Oracle

open RelCertifier.Parse

def arm_plateau_crit_cutsV2 : EvolStrengthening :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ] }

def arm_plateau_crit_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Accelerate", [⟨(.cmp "<=" (.var "v") (.num "0.355")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "1") (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "v") (.bin "*" (.num "1") (.bin "-" (.var "theta") (.num "0.5")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "theta") (.num "0.855")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "1") (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355"))]⟩]),
      ("Brake", [⟨(.cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "1") (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "theta") (.num "0.855")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "v") (.bin "*" (.num "1") (.bin "-" (.var "theta") (.num "0.5")))) (.num "0.355"))]⟩])
    ]
    R := [
      ("ApproachA", [⟨(.cmp ">=" (.var "theta") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("ApproachB", [⟨(.cmp ">=" (.var "theta") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("ApproachC", [⟨(.cmp ">=" (.var "theta") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("Hold", [⟨(.cmp ">=" (.var "theta") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "theta") (.num "1.15")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem arm_plateau_crit_cutsV2_wf : evolStrengtheningWF arm_plateau_crit_IRv2 arm_plateau_crit_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem arm_plateau_crit_cutsV2X_wf : evolStrengtheningWFX arm_plateau_crit_IRv2 arm_plateau_crit_cutsV2X = true := rfl

end RelCertifier.Oracle

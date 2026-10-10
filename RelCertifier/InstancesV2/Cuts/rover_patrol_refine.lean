/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_refine`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_patrol_refine

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_patrol_refine_cutsV2 : EvolStrengthening :=
  { L := [
      ("SLOW", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_ECO", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("MEDIUM_BRISK", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict)]),
      ("FAST", [((.cmp ">=" (.var "s") (.num "50.0")), CutRoute.diNonstrict)])
    ]
    R := [
      ("SLOW", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "0.6")), CutRoute.shape)]),
      ("MEDIUM_ECO", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "0.9")), CutRoute.shape)]),
      ("MEDIUM_BRISK", [((.cmp ">=" (.var "s") (.num "20.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.1")), CutRoute.shape)]),
      ("FAST", [((.cmp ">=" (.var "s") (.num "50.0")), CutRoute.diNonstrict), ((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.5")), CutRoute.shape)])
    ] }

def rover_patrol_refine_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("SLOW", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.8")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "0.8"))]⟩, ⟨(.cmp ">=" (.var "v") (.num "0.1")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.48")))) (.num "-0.95"))]⟩]),
      ("MEDIUM_ECO", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.1")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "0.95"))]⟩, ⟨(.cmp ">=" (.var "v") (.num "0.1")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.72")))) (.num "-1.55"))]⟩]),
      ("MEDIUM_BRISK", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.3")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "1.05"))]⟩, ⟨(.cmp ">=" (.var "v") (.num "0.1")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "0.88")))) (.num "-1.95"))]⟩]),
      ("FAST", [⟨(.cmp ">=" (.var "s") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "1.25")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.1")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "2.5") (.bin "-" (.var "v") (.num "1.2")))) (.num "-2.75"))]⟩])
    ]
    R := [
      ("SLOW", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MEDIUM_ECO", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.9")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MEDIUM_BRISK", [⟨(.cmp ">=" (.var "s") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.1")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FAST", [⟨(.cmp ">=" (.var "s") (.num "50.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "1.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_patrol_refine_cutsV2_wf : evolStrengtheningWF rover_patrol_refine_IRv2 rover_patrol_refine_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_patrol_refine_cutsV2X_wf : evolStrengtheningWFX rover_patrol_refine_IRv2 rover_patrol_refine_cutsV2X = true := rfl

end RelCertifier.Oracle

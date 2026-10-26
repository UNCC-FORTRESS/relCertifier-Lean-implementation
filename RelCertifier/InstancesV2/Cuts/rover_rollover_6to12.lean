/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_6to12` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_6to12`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.rover_rollover_6to12

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_rollover_6to12_cutsV2 : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict), ((.cmp "<=" (.var "v") (.num "0.65")), CutRoute.shape)])
    ] }

def rover_rollover_6to12_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.65")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.3")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.5")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.65")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem rover_rollover_6to12_cutsV2_wf : evolStrengtheningWF rover_rollover_6to12_IRv2 rover_rollover_6to12_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem rover_rollover_6to12_cutsV2X_wf : evolStrengtheningWFX rover_rollover_6to12_IRv2 rover_rollover_6to12_cutsV2X = true := rfl

end RelCertifier.Oracle

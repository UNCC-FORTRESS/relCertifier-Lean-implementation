/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story3_rollover_ladder_rung_b`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.story3_rollover_ladder_rung_b

namespace RelCertifier.Oracle

open RelCertifier.Parse

def story3_rollover_ladder_rung_b_cutsV2 : EvolStrengthening :=
  { L := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ]
    R := [
      ("STEEP", [((.cmp ">=" (.var "s") (.num "0.0")), CutRoute.diNonstrict)]),
      ("MODER", [((.cmp ">=" (.var "s") (.num "0.6")), CutRoute.diNonstrict)]),
      ("FLAT", [((.cmp ">=" (.var "s") (.num "1.4")), CutRoute.diNonstrict)])
    ] }

def story3_rollover_ladder_rung_b_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.var "psi") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_psi") (.bin "*" (.num "1") (.bin "-" (.var "psi") (.num "0")))) (.num "-0.5"))]⟩, ⟨(.cmp ">=" (.var "theta_p") (.num "-0.5")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "omega_theta") (.bin "*" (.num "1") (.bin "-" (.var "theta_p") (.num "0")))) (.num "-0.5"))]⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem story3_rollover_ladder_rung_b_cutsV2_wf : evolStrengtheningWF story3_rollover_ladder_rung_b_IRv2 story3_rollover_ladder_rung_b_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem story3_rollover_ladder_rung_b_cutsV2X_wf : evolStrengtheningWFX story3_rollover_ladder_rung_b_IRv2 story3_rollover_ladder_rung_b_cutsV2X = true := rfl

end RelCertifier.Oracle

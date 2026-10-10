/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story1_attdist_rung_a_6to8`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.story1_attdist_rung_a_6to8

namespace RelCertifier.Oracle

open RelCertifier.Parse

def story1_attdist_rung_a_6to8_cutsV2 : EvolStrengthening :=
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

def story1_attdist_rung_a_6to8_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ]
    R := [
      ("STEEP", [⟨(.cmp ">=" (.var "s") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("MODER", [⟨(.cmp ">=" (.var "s") (.num "0.6")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("FLAT", [⟨(.cmp ">=" (.var "s") (.num "1.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem story1_attdist_rung_a_6to8_cutsV2_wf : evolStrengtheningWF story1_attdist_rung_a_6to8_IRv2 story1_attdist_rung_a_6to8_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem story1_attdist_rung_a_6to8_cutsV2X_wf : evolStrengtheningWFX story1_attdist_rung_a_6to8_IRv2 story1_attdist_rung_a_6to8_cutsV2X = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_drag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.stopline_drag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def stopline_drag_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.35")), CutRoute.frozen)]),
      ("BRAKE", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.diNonstrict)]),
      ("STOP", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.35")), CutRoute.frozen)])
    ]
    R := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "0.35")), CutRoute.frozen)]),
      ("BRAKE", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.diNonstrict)]),
      ("STOP", [((.cmp ">=" (.var "p") (.num "100.0")), CutRoute.frozen), ((.cmp "<=" (.var "v") (.num "0.35")), CutRoute.frozen)])
    ] }

def stopline_drag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BRAKE", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ]
    R := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("BRAKE", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("STOP", [⟨(.cmp ">=" (.var "p") (.num "100.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "v") (.num "0.35")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem stopline_drag_cutsV2_wf : evolStrengtheningWF stopline_drag_IRv2 stopline_drag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem stopline_drag_cutsV2X_wf : evolStrengtheningWFX stopline_drag_IRv2 stopline_drag_cutsV2X = true := rfl

end RelCertifier.Oracle

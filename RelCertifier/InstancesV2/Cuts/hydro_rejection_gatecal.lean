/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hydro_rejection_gatecal` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py hydro_rejection_gatecal`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.hydro_rejection_gatecal

namespace RelCertifier.Oracle

open RelCertifier.Parse

def hydro_rejection_gatecal_cutsV2 : EvolStrengthening :=
  { L := [
      ("ONGRID", [((.cmp ">=" (.var "w") (.num "-0.004")), CutRoute.frozen), ((.cmp "<=" (.var "w") (.num "0.004")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "w") (.num "-1.0")), CutRoute.frozen), ((.cmp "<=" (.var "w") (.num "1.0")), CutRoute.frozen)]),
      ("REJECT", [((.cmp ">=" (.var "t") (.num "20.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "g") (.num "1.0")), CutRoute.shape), ((.cmp ">=" (.var "w") (.num "-1.0")), CutRoute.diStrict), ((.cmp "<=" (.var "w") (.num "1.0")), CutRoute.diStrict)])
    ]
    R := [
      ("ONGRID", [((.cmp ">=" (.var "w") (.num "-0.004")), CutRoute.frozen), ((.cmp "<=" (.var "w") (.num "0.004")), CutRoute.frozen), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "w") (.num "-1.0")), CutRoute.frozen), ((.cmp "<=" (.var "w") (.num "1.0")), CutRoute.frozen)]),
      ("REJECT", [((.cmp ">=" (.var "t") (.num "20.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "g") (.num "1.0")), CutRoute.shape), ((.cmp ">=" (.var "w") (.num "-1.0")), CutRoute.diStrict), ((.cmp "<=" (.var "w") (.num "1.0")), CutRoute.diStrict)])
    ] }

def hydro_rejection_gatecal_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("ONGRID", [⟨(.cmp ">=" (.var "w") (.num "-0.004")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "w") (.num "0.004")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "w") (.num "-1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "w") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("REJECT", [⟨(.cmp ">=" (.var "t") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "g") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "w") (.num "-1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("ONGRID", [⟨(.cmp ">=" (.var "w") (.num "-0.004")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "w") (.num "0.004")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "w") (.num "-1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "w") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("REJECT", [⟨(.cmp ">=" (.var "t") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "g") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "w") (.num "-1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "w") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem hydro_rejection_gatecal_cutsV2_wf : evolStrengtheningWF hydro_rejection_gatecal_IRv2 hydro_rejection_gatecal_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem hydro_rejection_gatecal_cutsV2X_wf : evolStrengtheningWFX hydro_rejection_gatecal_IRv2 hydro_rejection_gatecal_cutsV2X = true := rfl

end RelCertifier.Oracle

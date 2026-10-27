/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `ventilator_vc_cuffleak` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py ventilator_vc_cuffleak`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.ventilator_vc_cuffleak

namespace RelCertifier.Oracle

open RelCertifier.Parse

def ventilator_vc_cuffleak_cutsV2 : EvolStrengthening :=
  { L := [
      ("INSP", [((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "V") (.num "-0.4")), CutRoute.diStrict), ((.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutRoute.diStrict)]),
      ("EXP", [((.cmp ">=" (.var "t") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "V") (.num "-0.4")), CutRoute.diStrict), ((.cmp "<=" (.var "V") (.num "0.404")), CutRoute.diStrict), ((.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("INSP", [((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "V") (.num "-0.4")), CutRoute.diStrict), ((.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutRoute.diNonstrict)]),
      ("EXP", [((.cmp ">=" (.var "t") (.num "1.0")), CutRoute.diStrict), ((.cmp ">=" (.var "t") (.num "0.0")), CutRoute.diStrict), ((.cmp ">=" (.var "V") (.num "-0.4")), CutRoute.diStrict), ((.cmp "<=" (.var "V") (.num "0.404")), CutRoute.diStrict), ((.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutRoute.diStrict)])
    ] }

def ventilator_vc_cuffleak_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("INSP", [⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("EXP", [⟨(.cmp ">=" (.var "t") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "V") (.num "0.404")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("INSP", [⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diNonstrict, []⟩]),
      ("EXP", [⟨(.cmp ">=" (.var "t") (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "t") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "V") (.num "-0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.var "V") (.num "0.404")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp "<=" (.bin "-" (.var "V") (.bin "*" (.num "0.4") (.var "t"))) (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem ventilator_vc_cuffleak_cutsV2_wf : evolStrengtheningWF ventilator_vc_cuffleak_IRv2 ventilator_vc_cuffleak_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem ventilator_vc_cuffleak_cutsV2X_wf : evolStrengtheningWFX ventilator_vc_cuffleak_IRv2 ventilator_vc_cuffleak_cutsV2X = true := rfl

end RelCertifier.Oracle

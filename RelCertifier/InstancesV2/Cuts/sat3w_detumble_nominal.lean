/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_nominal` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py sat3w_detumble_nominal`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.sat3w_detumble_nominal

namespace RelCertifier.Oracle

open RelCertifier.Parse

def sat3w_detumble_nominal_cutsV2 : EvolStrengthening :=
  { L := [
      ("DETUMBLE", [((.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")), CutRoute.diStrict)])
    ]
    R := [
      ("DETUMBLE", [((.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")), CutRoute.diStrict)]),
      ("SAFE", [])
    ] }

def sat3w_detumble_nominal_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("DETUMBLE", [⟨(.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("DETUMBLE", [⟨(.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩]),
      ("SAFE", [⟨(.cmp ">=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.var "w1") (.var "w1")) (.num "2")) (.bin "*" (.bin "*" (.var "w2") (.var "w2")) (.num "4"))) (.bin "*" (.bin "*" (.var "w3") (.var "w3")) (.num "5"))) (.num "1.0")), CutKind.closure, CutEntry.weakening, CutRouteX.frozen, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem sat3w_detumble_nominal_cutsV2_wf : evolStrengtheningWF sat3w_detumble_nominal_IRv2 sat3w_detumble_nominal_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem sat3w_detumble_nominal_cutsV2X_wf : evolStrengtheningWFX sat3w_detumble_nominal_IRv2 sat3w_detumble_nominal_cutsV2X = true := rfl

end RelCertifier.Oracle

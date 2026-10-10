/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_tune_lag`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.acc_tune_lag

namespace RelCertifier.Oracle

open RelCertifier.Parse

def acc_tune_lag_cutsV2 : EvolStrengthening :=
  { L := [
      ("CRUISE", [])
    ]
    R := [
      ("CRUISE", [((.cmp ">=" (.var "v") (.num "20.0")), CutRoute.shape)]),
      ("DISENGAGE", [])
    ] }

def acc_tune_lag_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("CRUISE", [⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1") (.bin "-" (.var "v") (.num "30")))) (.num "2")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1") (.bin "-" (.var "v") (.num "30")))) (.num "-7")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "3") (.bin "-" (.var "v") (.num "30")))) (.num "2")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "3") (.bin "-" (.var "v") (.num "30")))) (.num "-17")), CutKind.linearForm, CutEntry.rational, CutRouteX.linearShape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "32")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp "<=" (.bin "+" (.var "a") (.bin "*" (.num "1") (.bin "-" (.var "v") (.num "30")))) (.num "2"))]⟩, ⟨(.cmp ">=" (.var "v") (.num "23")), CutKind.derivedBound, CutEntry.rational, CutRouteX.derivedShape, [(.cmp ">=" (.bin "+" (.var "a") (.bin "*" (.num "1") (.bin "-" (.var "v") (.num "30")))) (.num "-7"))]⟩])
    ]
    R := [
      ("CRUISE", [⟨(.cmp ">=" (.var "v") (.num "20.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "v") (.num "40.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("DISENGAGE", [⟨(.cmp "<=" (.var "v") (.num "20.0")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem acc_tune_lag_cutsV2_wf : evolStrengtheningWF acc_tune_lag_IRv2 acc_tune_lag_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem acc_tune_lag_cutsV2X_wf : evolStrengtheningWFX acc_tune_lag_IRv2 acc_tune_lag_cutsV2X = true := rfl

end RelCertifier.Oracle

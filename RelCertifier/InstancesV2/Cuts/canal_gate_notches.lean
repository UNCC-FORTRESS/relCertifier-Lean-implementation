/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `canal_gate_notches` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py canal_gate_notches`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.canal_gate_notches

namespace RelCertifier.Oracle

open RelCertifier.Parse

def canal_gate_notches_cutsV2 : EvolStrengthening :=
  { L := [
      ("RAISE", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape)]),
      ("HOLD", [((.cmp ">=" (.var "h") (.num "0.4")), CutRoute.shape)]),
      ("LOWER", [((.cmp "<=" (.var "h") (.num "1.2")), CutRoute.shape)])
    ]
    R := [
      ("N100", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape)]),
      ("N75", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "h") (.num "1.2")), CutRoute.shape)]),
      ("N50", [((.cmp ">=" (.var "h") (.num "0.0")), CutRoute.shape), ((.cmp "<=" (.var "h") (.num "1.2")), CutRoute.shape)]),
      ("N25", [((.cmp "<=" (.var "h") (.num "1.2")), CutRoute.shape)])
    ] }

def canal_gate_notches_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("RAISE", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "0.95")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("HOLD", [⟨(.cmp ">=" (.var "h") (.num "0.4")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "0.9")), CutKind.closure, CutEntry.weakening, CutRouteX.shape, []⟩]),
      ("LOWER", [⟨(.cmp "<=" (.var "h") (.num "1.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.3")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ]
    R := [
      ("N100", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "1")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩]),
      ("N75", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "1.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("N50", [⟨(.cmp ">=" (.var "h") (.num "0.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp "<=" (.var "h") (.num "1.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩]),
      ("N25", [⟨(.cmp "<=" (.var "h") (.num "1.2")), CutKind.guardConj, CutEntry.membership, CutRouteX.shape, []⟩, ⟨(.cmp ">=" (.var "h") (.num "0.25")), CutKind.impliedContract, CutEntry.rational, CutRouteX.shape, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem canal_gate_notches_cutsV2_wf : evolStrengtheningWF canal_gate_notches_IRv2 canal_gate_notches_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem canal_gate_notches_cutsV2X_wf : evolStrengtheningWFX canal_gate_notches_IRv2 canal_gate_notches_cutsV2X = true := rfl

end RelCertifier.Oracle

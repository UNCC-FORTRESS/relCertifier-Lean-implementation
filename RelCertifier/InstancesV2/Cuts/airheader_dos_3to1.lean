/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `airheader_dos_3to1` (suite_v2) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py airheader_dos_3to1`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.airheader_dos_3to1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def airheader_dos_3to1_cutsV2 : EvolStrengthening :=
  { L := [
      ("NORMAL", [((.cmp "<=" (.var "p") (.num "9.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)]),
      ("ALARM", [((.cmp ">=" (.var "p") (.num "5.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)]),
      ("TRIP", [((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)])
    ]
    R := [
      ("NORMAL", [((.cmp "<=" (.var "p") (.num "9.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)]),
      ("ALARM", [((.cmp ">=" (.var "p") (.num "5.0")), CutRoute.diStrict), ((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)]),
      ("TRIP", [((.cmp ">=" (.var "g") (.num "0.02")), CutRoute.frozen), ((.cmp "<=" (.var "g") (.num "0.06")), CutRoute.frozen)])
    ] }

def airheader_dos_3to1_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("NORMAL", [⟨(.cmp "<=" (.var "p") (.num "9.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("ALARM", [⟨(.cmp ">=" (.var "p") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("TRIP", [⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "5.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩])
    ]
    R := [
      ("NORMAL", [⟨(.cmp "<=" (.var "p") (.num "9.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("ALARM", [⟨(.cmp ">=" (.var "p") (.num "5.0")), CutKind.guardConj, CutEntry.membership, CutRouteX.diStrict, []⟩, ⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩]),
      ("TRIP", [⟨(.cmp ">=" (.var "g") (.num "0.02")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "g") (.num "0.06")), CutKind.guardConj, CutEntry.membership, CutRouteX.frozen, []⟩, ⟨(.cmp "<=" (.var "p") (.num "5.0")), CutKind.closure, CutEntry.weakening, CutRouteX.diStrict, []⟩])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem airheader_dos_3to1_cutsV2_wf : evolStrengtheningWF airheader_dos_3to1_IRv2 airheader_dos_3to1_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem airheader_dos_3to1_cutsV2X_wf : evolStrengtheningWFX airheader_dos_3to1_IRv2 airheader_dos_3to1_cutsV2X = true := rfl

end RelCertifier.Oracle

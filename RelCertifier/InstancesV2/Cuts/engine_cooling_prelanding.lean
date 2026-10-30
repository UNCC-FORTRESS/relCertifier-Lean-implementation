/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `engine_cooling_prelanding` (prelanding_demo) — checked-cut certificates, legacy and extended (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Checker.EvolStrengtheningX
import RelCertifier.InstancesV2.BenchIR.engine_cooling_prelanding

namespace RelCertifier.Oracle

open RelCertifier.Parse

def engine_cooling_prelanding_cutsV2 : EvolStrengthening :=
  { L := [
      ("Cool", []),
      ("Heat", [])
    ]
    R := [
      ("Cool", []),
      ("Heat", [])
    ] }

def engine_cooling_prelanding_cutsV2X : EvolStrengtheningX :=
  { L := [
      ("Cool", []),
      ("Heat", [])
    ]
    R := [
      ("Cool", []),
      ("Heat", [])
    ] }

/-- The legacy (guard-conjunct) part is well formed. -/
theorem engine_cooling_prelanding_cutsV2_wf : evolStrengtheningWF engine_cooling_prelanding_IRv2 engine_cooling_prelanding_cutsV2 = true := rfl

/-- The extended certificate is well formed (every kind, entry and rational route
re-checked; `CutLiftX.evolStrengtheningWFX_entryL/R` consume it). -/
theorem engine_cooling_prelanding_cutsV2X_wf : evolStrengtheningWFX engine_cooling_prelanding_IRv2 engine_cooling_prelanding_cutsV2X = true := rfl

end RelCertifier.Oracle

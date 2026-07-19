/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_low` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.plant_fan_low

namespace RelCertifier.Oracle

open RelCertifier.Parse

def plant_fan_low_cuts : EvolStrengthening :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("Approach", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("Return", [])
    ] }

example : evolStrengtheningWF plant_fan_low_IR plant_fan_low_cuts = true := rfl

end RelCertifier.Oracle

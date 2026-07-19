/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_mid` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.plant_fan_mid

namespace RelCertifier.Oracle

open RelCertifier.Parse

def plant_fan_mid_cuts : EvolStrengthening :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachFast", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachSlow", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF plant_fan_mid_IR plant_fan_mid_cuts = true := rfl

end RelCertifier.Oracle

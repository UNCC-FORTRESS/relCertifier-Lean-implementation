/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_high` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.plant_fan_high

namespace RelCertifier.Oracle

open RelCertifier.Parse

def plant_fan_high_cuts : EvolStrengthening :=
  { L := [
      ("Accelerate", []),
      ("Brake", [])
    ]
    R := [
      ("ApproachA", [((.cmp ">=" (.var "theta") (.num "0.0")), CutRoute.diStrict)]),
      ("ApproachB", [((.cmp ">=" (.var "theta") (.num "0.35")), CutRoute.diStrict)]),
      ("ApproachC", [((.cmp ">=" (.var "theta") (.num "0.5")), CutRoute.diStrict)]),
      ("Hold", [((.cmp ">=" (.var "theta") (.num "0.6")), CutRoute.frozen)])
    ] }

example : evolStrengtheningWF plant_fan_high_IR plant_fan_high_cuts = true := rfl

end RelCertifier.Oracle

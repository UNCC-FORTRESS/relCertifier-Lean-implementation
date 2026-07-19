/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_M1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover3tier_M1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover3tier_M1_cuts : EvolStrengthening :=
  { L := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ]
    R := [
      ("ACCEL", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.shape)]),
      ("COAST", [])
    ] }

example : evolStrengtheningWF rover3tier_M1_IR rover3tier_M1_cuts = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_r1` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_tier_r1

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_tier_r1_cuts : EvolStrengthening :=
  { L := [
      ("Cruise", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diNonstrict)])
    ]
    R := [
      ("Cruise", [((.cmp ">=" (.var "v") (.num "0.3")), CutRoute.diStrict)])
    ] }

example : evolStrengtheningWF rover_tier_r1_IR rover_tier_r1_cuts = true := rfl

end RelCertifier.Oracle

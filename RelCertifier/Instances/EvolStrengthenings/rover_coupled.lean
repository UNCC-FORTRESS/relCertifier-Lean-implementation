/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_coupled` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.rover_coupled

namespace RelCertifier.Oracle

open RelCertifier.Parse

def rover_coupled_cuts : EvolStrengthening :=
  { L := [
      ("Drive", []),
      ("Drift", []),
      ("Stop", [])
    ]
    R := [
      ("Recover", [((.cmp ">=" (.var "vx") (.num "0.25")), CutRoute.diStrict)]),
      ("Drive", [((.cmp ">=" (.var "vx") (.num "0.3")), CutRoute.diStrict)]),
      ("Safe", [((.cmp ">=" (.var "vx") (.num "0.75")), CutRoute.frozen), ((.cmp "<=" (.var "vx") (.num "1.0")), CutRoute.frozen)])
    ] }

example : evolStrengtheningWF rover_coupled_IR rover_coupled_cuts = true := rfl

end RelCertifier.Oracle

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `attitude_rate` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.attitude_rate

namespace RelCertifier.Oracle

open RelCertifier.Parse

def attitude_rate_cuts : EvolStrengthening :=
  { L := [
      ("CRUISE", [((.cmp ">=" (.var "p") (.num "0.0")), CutRoute.diStrict)])
    ]
    R := [
      ("RECOVER", [((.cmp ">=" (.var "p") (.num "0.0")), CutRoute.diStrict)]),
      ("TRACK", [((.cmp ">=" (.var "p") (.num "0.5")), CutRoute.diStrict), ((.cmp "<=" (.var "p") (.num "1.15")), CutRoute.diStrict)])
    ] }

example : evolStrengtheningWF attitude_rate_IR attitude_rate_cuts = true := rfl

end RelCertifier.Oracle

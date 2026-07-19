/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `match_multi_rate` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.match_multi_rate

namespace RelCertifier.Oracle

open RelCertifier.Parse

def match_multi_rate_cuts : EvolStrengthening :=
  { L := [
      ("FAST", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape)]),
      ("MEDIUM", [((.cmp ">=" (.var "v") (.num "0.5")), CutRoute.shape)]),
      ("SLOW", [((.cmp ">=" (.var "v") (.num "0.7")), CutRoute.shape)]),
      ("RESET", [])
    ]
    R := [
      ("DRIVE", [((.cmp ">=" (.var "v") (.num "0.2")), CutRoute.shape), ((.cmp "<=" (.var "v") (.num "1.0")), CutRoute.shape)])
    ] }

example : evolStrengtheningWF match_multi_rate_IR match_multi_rate_cuts = true := rfl

end RelCertifier.Oracle

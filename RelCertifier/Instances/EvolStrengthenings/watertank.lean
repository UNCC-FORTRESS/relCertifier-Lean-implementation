/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` — checked-cut strengthening (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cuts`.
-/
import RelCertifier.Checker.EvolStrengthening
import RelCertifier.Instances.BenchIR.watertank

namespace RelCertifier.Oracle

open RelCertifier.Parse

def watertank_cuts : EvolStrengthening :=
  { L := [
      ("Low", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict)]),
      ("Mid", [((.cmp ">=" (.var "x") (.num "13.0")), CutRoute.diStrict)]),
      ("High", [])
    ]
    R := [
      ("Low", [((.cmp ">=" (.var "x") (.num "0.0")), CutRoute.diStrict)]),
      ("Mid", [((.cmp ">=" (.var "x") (.num "10.0")), CutRoute.diStrict)]),
      ("High", [])
    ] }

example : evolStrengtheningWF watertank_IR watertank_cuts = true := rfl

end RelCertifier.Oracle

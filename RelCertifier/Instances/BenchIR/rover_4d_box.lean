/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_4d_box` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_4d_box/input.txt` (do not edit). -/
def rover_4d_box_IR : PProblem :=
  {
    name := "rover_4d_box"
    lambdaMin := "1.0"
    lambdaMax := "3.0"
    L := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "HOLD"
          odes := [("px", (.num "0")),
            ("py", (.num "0")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "9.0")) (.cmp "<=" (.var "px") (.num "11.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "9.0")) (.cmp "<=" (.var "px") (.num "11.1"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.1"))) (.cmp ">=" (.var "vx") (.num "0.0"))) (.cmp "<=" (.var "vx") (.num "2.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["HOLD"] } ] }
    R := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "APPROACH"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.bin "-" (.num "0.65") (.var "vx"))),
            ("vy", (.bin "-" (.num "0.0") (.var "vy")))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.7")) (.cmp "<=" (.var "vx") (.num "1.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "1.5"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["SETTLE", "APPROACH"] },
        {
          name := "SETTLE"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "0.7")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "1.5"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["SETTLE"] } ] }
    invariants := [
      ("HOLD", (.cmp "<=" (.bin "-" (.var "L_px") (.var "R_px")) (.num "0.5")))] }

end RelCertifier.Parse

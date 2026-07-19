/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3_M1` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover3_M1/input.txt` (do not edit). -/
def rover3_M1_IR : PProblem :=
  {
    name := "rover3_M1"
    lambdaMin := "1.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["px", "vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("vx", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "0.0")) (.cmp "<=" (.var "px") (.num "5.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0")))
          next := ["Drift", "Drive"] },
        {
          name := "Drift"
          odes := [("px", (.var "vx")),
            ("vx", (.num "0.1"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "5.0")) (.cmp "<=" (.var "px") (.num "10.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0")))
          next := ["Stop", "Drift"] },
        {
          name := "Stop"
          odes := [("px", (.var "vx")),
            ("vx", (.bin "*" (.num "-0.5") (.var "vx")))]
          guard := (.and (.cmp ">=" (.var "px") (.num "10.0")) (.cmp "<" (.var "px") (.num "10.75")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0")))
          next := ["Stop"] } ] }
    R := {
      stateVars := ["px", "vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Recover"
          odes := [("px", (.var "vx")),
            ("vx", (.num "0.4"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.25")) (.cmp "<=" (.var "vx") (.num "0.3")))
          evolve := (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1")))
          next := ["Drive", "Recover"] },
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("vx", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.3")) (.cmp "<" (.var "vx") (.num "0.75")))
          evolve := (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1")))
          next := ["Safe", "Drive"] },
        {
          name := "Safe"
          odes := [("px", (.var "vx")),
            ("vx", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.75")) (.cmp "<=" (.var "vx") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1")))
          next := ["Safe"] } ] }
    invariants := [
      ("Drive", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "0.5")))),
      ("Drift", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "1.0")))),
      ("Stop", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "2.0"))))] }

end RelCertifier.Parse

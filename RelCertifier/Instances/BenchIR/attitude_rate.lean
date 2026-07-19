/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `attitude_rate` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/attitude_rate/input.txt` (do not edit). -/
def attitude_rate_IR : PProblem :=
  {
    name := "attitude_rate"
    lambdaMin := "2.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["phi", "p", "theta", "q", "psi", "r"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("phi", (.var "p")),
            ("p", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.var "p"))) (.bin "*" (.num "0.05") (.var "q")))),
            ("theta", (.var "q")),
            ("q", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "0.5") (.var "q"))) (.bin "*" (.num "0.05") (.var "p")))),
            ("psi", (.var "r")),
            ("r", (.bin "-" (.num "0.5") (.bin "*" (.num "0.3") (.var "r"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "0.85")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "-0.05")) (.cmp "<=" (.var "p") (.num "1.0"))) (.cmp ">=" (.var "phi") (.num "-1.0"))) (.cmp "<=" (.var "phi") (.num "1.0"))) (.cmp ">=" (.var "psi") (.num "-1.0"))) (.cmp "<=" (.var "psi") (.num "1.0"))) (.cmp ">=" (.var "q") (.num "0.0"))) (.cmp "<=" (.var "q") (.num "1.0"))) (.cmp ">=" (.var "r") (.num "0.0"))) (.cmp "<=" (.var "r") (.num "2.0"))) (.cmp ">=" (.var "theta") (.num "-1.0"))) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["CRUISE"] } ] }
    R := {
      stateVars := ["phi", "p", "theta", "q", "psi", "r"]
      epsilon := "2.0"
      modes := [
        {
          name := "RECOVER"
          odes := [("phi", (.var "p")),
            ("p", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "1.0") (.var "p"))) (.bin "*" (.num "0.05") (.var "q")))),
            ("theta", (.var "q")),
            ("q", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "1.0") (.var "q"))) (.bin "*" (.num "0.05") (.var "p")))),
            ("psi", (.var "r")),
            ("r", (.bin "-" (.num "0.5") (.bin "*" (.num "0.8") (.var "r"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "-0.05")) (.cmp "<=" (.var "p") (.num "1.2"))) (.cmp ">=" (.var "q") (.num "0.0"))) (.cmp "<=" (.var "q") (.num "1.2"))) (.cmp ">=" (.var "r") (.num "0.0"))) (.cmp "<=" (.var "r") (.num "1.0")))
          next := ["TRACK", "RECOVER"] },
        {
          name := "TRACK"
          odes := [("phi", (.var "p")),
            ("p", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "1.0") (.var "p"))) (.bin "*" (.num "0.05") (.var "q")))),
            ("theta", (.var "q")),
            ("q", (.bin "+" (.bin "-" (.num "1.0") (.bin "*" (.num "1.0") (.var "q"))) (.bin "*" (.num "0.05") (.var "p")))),
            ("psi", (.var "r")),
            ("r", (.bin "-" (.num "0.5") (.bin "*" (.num "0.8") (.var "r"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "0.5")) (.cmp "<=" (.var "p") (.num "1.15")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "p") (.num "-0.05")) (.cmp "<=" (.var "p") (.num "1.2"))) (.cmp ">=" (.var "q") (.num "0.0"))) (.cmp "<=" (.var "q") (.num "1.2"))) (.cmp ">=" (.var "r") (.num "0.0"))) (.cmp "<=" (.var "r") (.num "1.0")))
          next := ["TRACK"] } ] }
    invariants := [
      ("CRUISE", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "0.5"))))] }

end RelCertifier.Parse

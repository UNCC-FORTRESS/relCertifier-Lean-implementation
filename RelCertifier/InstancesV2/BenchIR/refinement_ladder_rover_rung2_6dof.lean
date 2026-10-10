/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_6dof` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung2_6dof`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/refinement_ladder_rover_rung2_6dof/input.txt` (do not edit). -/
def refinement_ladder_rover_rung2_6dof_IRv2 : PProblem :=
  {
    name := "refinement_ladder_rover_rung2_6dof"
    lambdaMin := "1.001"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0"))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0"))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0")))] }

end RelCertifier.Parse

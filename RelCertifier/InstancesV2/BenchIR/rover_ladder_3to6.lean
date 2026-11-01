/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_3to6` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_3to6`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rover_ladder_3to6/input.txt` (do not edit). -/
def rover_ladder_3to6_IRv2 : PProblem :=
  {
    name := "rover_ladder_3to6"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.num "0.15")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.1")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.num "0.05")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.num "0.05")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "0.015") (.bin "*" (.var "v") (.bin "*" (.num "-1") (.var "psi"))))))]
          guard := (.cmp ">=" (.var "s") (.num "140.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "3.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "60.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "5.0") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "60.0")) (.cmp "<" (.var "s") (.num "140.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "6.5") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "140.0"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "8.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "z") (.num "-0.15"))) (.cmp "<=" (.var "z") (.num "0.15"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.var "R_psi")) (.cmp "<=" (.var "R_psi") (.var "L_psi")))) (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p"))))),
      ("MODER", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.var "R_psi")) (.cmp "<=" (.var "R_psi") (.var "L_psi")))) (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p"))))),
      ("FLAT", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.and (.cmp "<=" (.var "L_psi") (.var "R_psi")) (.cmp "<=" (.var "R_psi") (.var "L_psi")))) (.and (.cmp "<=" (.var "L_theta_p") (.num "0.25")) (.cmp "<=" (.bin "-" (.num "0") (.num "0.25")) (.var "L_theta_p")))))] }

end RelCertifier.Parse

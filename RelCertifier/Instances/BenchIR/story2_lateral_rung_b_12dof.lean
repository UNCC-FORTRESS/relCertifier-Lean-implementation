/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story2_lateral_rung_b_12dof` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/story2_lateral_rung_b_12dof/input.txt` (do not edit). -/
def story2_lateral_rung_b_12dof_IR : PProblem :=
  {
    name := "story2_lateral_rung_b_12dof"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "y2", "z", "phi_r", "w", "w2", "w3", "w4"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-0.75") (.var "y"))),
            ("y2", (.bin "*" (.num "-0.75") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.bin "*" (.num "-1") (.var "w2"))),
            ("w3", (.bin "*" (.num "-1") (.var "w3"))),
            ("w4", (.bin "*" (.num "-1") (.var "w4")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "0.15"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "0.15"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-0.75") (.var "y"))),
            ("y2", (.bin "*" (.num "-0.75") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.bin "*" (.num "-1") (.var "w2"))),
            ("w3", (.bin "*" (.num "-1") (.var "w3"))),
            ("w4", (.bin "*" (.num "-1") (.var "w4")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "0.15"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "0.15"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-0.75") (.var "y"))),
            ("y2", (.bin "*" (.num "-0.75") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.bin "*" (.num "-1") (.var "w2"))),
            ("w3", (.bin "*" (.num "-1") (.var "w3"))),
            ("w4", (.bin "*" (.num "-1") (.var "w4")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "0.15"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "0.15"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "y2", "z", "phi_r", "w", "w2", "w3", "w4"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("y2", (.bin "*" (.num "-1.0") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.num "0")),
            ("w3", (.num "0")),
            ("w4", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.1"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.1"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "1.1"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("y2", (.bin "*" (.num "-1.0") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.num "0")),
            ("w3", (.num "0")),
            ("w4", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.1"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.1"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "1.1"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("y2", (.bin "*" (.num "-1.0") (.var "y2"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w"))),
            ("w2", (.num "0")),
            ("w3", (.num "0")),
            ("w4", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "w2") (.num "-1.0"))) (.cmp "<=" (.var "w2") (.num "1.1"))) (.cmp ">=" (.var "w3") (.num "-1.0"))) (.cmp "<=" (.var "w3") (.num "1.1"))) (.cmp ">=" (.var "w4") (.num "-1.0"))) (.cmp "<=" (.var "w4") (.num "1.1"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "y2") (.num "0.0"))) (.cmp "<=" (.var "y2") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_y2") (.bin "+" (.var "R_y2") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("MODER", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_y2") (.bin "+" (.var "R_y2") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("FLAT", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_y2") (.bin "+" (.var "R_y2") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p"))))] }

end RelCertifier.Parse

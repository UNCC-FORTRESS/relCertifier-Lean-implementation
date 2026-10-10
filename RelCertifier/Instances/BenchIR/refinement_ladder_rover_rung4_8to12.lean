/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung4_8to12` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/refinement_ladder_rover_rung4_8to12/input.txt` (byte-identical to the retired legacy file it was emitted from; do not edit). -/
def refinement_ladder_rover_rung4_8to12_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung4_8to12"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("z", (.var "omega_z")),
            ("omega_z", (.bin "-" (.bin "*" (.num "-1") (.var "z")) (.bin "*" (.num "2") (.var "omega_z")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("y", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("z", (.var "omega_z")),
            ("omega_z", (.bin "-" (.bin "*" (.num "-1") (.var "z")) (.bin "*" (.num "2") (.var "omega_z")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("y", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("z", (.var "omega_z")),
            ("omega_z", (.bin "-" (.bin "*" (.num "-1") (.var "z")) (.bin "*" (.num "2") (.var "omega_z")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("y", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "y")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "omega_z", "phi_r", "omega_phi", "y", "omega_y"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "*" (.num "-1") (.var "omega_theta"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("omega_z", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "*" (.num "-1") (.var "omega_theta"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("omega_z", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "*" (.num "-1") (.var "omega_theta"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("omega_z", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

end RelCertifier.Parse

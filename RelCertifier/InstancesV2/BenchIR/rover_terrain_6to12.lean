/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to12` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_6to12`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/rover_terrain_6to12/input.txt` (do not edit). -/
def rover_terrain_6to12_IRv2 : PProblem :=
  {
    name := "rover_terrain_6to12"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.bin "*" (.num "0.1") (.var "ax"))) (.bin "*" (.num "0.5") (.var "z")))),
            ("phi_r", (.bin "-" (.var "omega_phi") (.var "phi_r"))),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "omega_phi")) (.bin "*" (.num "0.1") (.var "ay")))),
            ("z", (.bin "-" (.var "vz") (.var "z"))),
            ("vz", (.bin "*" (.num "-1") (.var "vz"))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v"))) (.var "ax")))),
            ("ay", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.var "ay"))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.5")) (.cmp "<=" (.var "ax") (.num "1.95"))) (.cmp ">=" (.var "ay") (.num "-1.6"))) (.cmp "<=" (.var "ay") (.num "1.6"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-1.0"))) (.cmp "<=" (.var "phi_r") (.num "1.0"))) (.cmp ">=" (.var "psi") (.num "-1.0"))) (.cmp "<=" (.var "psi") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-1.0"))) (.cmp "<=" (.var "theta_p") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.bin "*" (.num "0.1") (.var "ax"))) (.bin "*" (.num "0.5") (.var "z")))),
            ("phi_r", (.bin "-" (.var "omega_phi") (.var "phi_r"))),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "omega_phi")) (.bin "*" (.num "0.1") (.var "ay")))),
            ("z", (.bin "-" (.var "vz") (.var "z"))),
            ("vz", (.bin "*" (.num "-1") (.var "vz"))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v"))) (.var "ax")))),
            ("ay", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.var "ay"))))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.5")) (.cmp "<=" (.var "ax") (.num "1.95"))) (.cmp ">=" (.var "ay") (.num "-1.6"))) (.cmp "<=" (.var "ay") (.num "1.6"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-1.0"))) (.cmp "<=" (.var "phi_r") (.num "1.0"))) (.cmp ">=" (.var "psi") (.num "-1.0"))) (.cmp "<=" (.var "psi") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-1.0"))) (.cmp "<=" (.var "theta_p") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "-" (.var "omega_psi") (.var "psi"))),
            ("omega_psi", (.bin "*" (.num "-1") (.var "omega_psi"))),
            ("theta_p", (.bin "-" (.var "omega_theta") (.var "theta_p"))),
            ("omega_theta", (.bin "+" (.bin "+" (.bin "*" (.num "-1") (.var "omega_theta")) (.bin "*" (.num "0.1") (.var "ax"))) (.bin "*" (.num "0.5") (.var "z")))),
            ("phi_r", (.bin "-" (.var "omega_phi") (.var "phi_r"))),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "omega_phi")) (.bin "*" (.num "0.1") (.var "ay")))),
            ("z", (.bin "-" (.var "vz") (.var "z"))),
            ("vz", (.bin "*" (.num "-1") (.var "vz"))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v"))) (.var "ax")))),
            ("ay", (.bin "*" (.num "5") (.bin "-" (.bin "*" (.var "v") (.bin "-" (.var "omega_psi") (.var "psi"))) (.var "ay"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.5")) (.cmp "<=" (.var "ax") (.num "1.95"))) (.cmp ">=" (.var "ay") (.num "-1.6"))) (.cmp "<=" (.var "ay") (.num "1.6"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-1.0"))) (.cmp "<=" (.var "phi_r") (.num "1.0"))) (.cmp ">=" (.var "psi") (.num "-1.0"))) (.cmp "<=" (.var "psi") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-1.0"))) (.cmp "<=" (.var "theta_p") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("vz", (.num "0")),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.1"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("vz", (.num "0")),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.1"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))) (.bin "*" (.num "0.2") (.bin "*" (.var "phi_r") (.var "phi_r")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "0.5") (.var "z")))),
            ("omega_theta", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("vz", (.num "0")),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.1"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s")))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s")))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))))] }

end RelCertifier.Parse

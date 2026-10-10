/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_a_6to8` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/story1_attdist_rung_a_6to8/input.txt` (byte-identical to the retired legacy file it was emitted from; do not edit). -/
def story1_attdist_rung_a_6to8_IR : PProblem :=
  {
    name := "story1_attdist_rung_a_6to8"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
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
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.6")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
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
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.6")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
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
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.6")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.5")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.5")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.5")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.bin "*" (.bin "-" (.var "L_omega_psi") (.var "L_psi")) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.num "0.25"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.bin "*" (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.num "0.25")))),
      ("MODER", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.bin "*" (.bin "-" (.var "L_omega_psi") (.var "L_psi")) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.bin "*" (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.num "0.25")))),
      ("FLAT", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.bin "*" (.bin "-" (.var "L_omega_psi") (.var "L_psi")) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.bin "*" (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))) (.num "0.25"))))] }

end RelCertifier.Parse

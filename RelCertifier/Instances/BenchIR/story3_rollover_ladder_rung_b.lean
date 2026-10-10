/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` — parser-emitted IR literal (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-ir`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of the retired legacy `story3_rollover_ladder_rung_b` file (`benchmarks/suite_uniform/`, removed from the tree; git history keeps it). Not the suite_v2 file: only its right system and invariant rows are used, by `rfl` identities in `InstancesV2/Modal/Story3RolloverRungB` (do not edit). -/
def story3_rollover_ladder_rung_b_IR : PProblem :=
  {
    name := "story3_rollover_ladder_rung_b"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]
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
            ("e", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-4") (.var "e")) (.bin "*" (.num "4") (.var "r")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("e", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-4") (.var "e")) (.bin "*" (.num "4") (.var "r")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("e", (.var "r")),
            ("r", (.bin "-" (.bin "*" (.num "-4") (.var "e")) (.bin "*" (.num "4") (.var "r")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "e", "r", "phi_r", "omega_phi", "z", "y"]
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
            ("e", (.bin "-" (.var "r") (.bin "*" (.num "2") (.var "e")))),
            ("r", (.bin "*" (.num "-2") (.var "r"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.52")) (.cmp "<=" (.var "e") (.num "1.52"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-3.04"))) (.cmp "<=" (.var "r") (.num "3.04"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "-" (.var "r") (.bin "*" (.num "2") (.var "e")))),
            ("r", (.bin "*" (.num "-2") (.var "r"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.52")) (.cmp "<=" (.var "e") (.num "1.52"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-3.04"))) (.cmp "<=" (.var "r") (.num "3.04"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "-" (.var "r") (.bin "*" (.num "2") (.var "e")))),
            ("r", (.bin "*" (.num "-2") (.var "r"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.52")) (.cmp "<=" (.var "e") (.num "1.52"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-3.04"))) (.cmp "<=" (.var "r") (.num "3.04"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.var "L_omega_psi"))) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.25"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.var "L_omega_theta"))) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.25")))),
      ("MODER", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.var "L_omega_psi"))) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.var "L_omega_theta"))) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.25")))),
      ("FLAT", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.var "L_omega_psi"))) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.var "L_omega_theta"))) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.25"))))] }

end RelCertifier.Parse

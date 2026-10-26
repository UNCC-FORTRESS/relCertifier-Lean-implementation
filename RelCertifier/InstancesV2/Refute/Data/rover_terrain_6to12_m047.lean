/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to12_m047`: a mutant of `rover_terrain_6to12` and its refutation witness (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= L_omega_phs 0.1) [L_omega_phs->R_omega_phs]` of `benchmarks/suite_v2/rover_terrain_6to12`; file `benchmarks/refute_mutants/rover_terrain_6to12_m047/input.txt`.
-/
import RelCertifier.Trusted.Parse
import RelCertifier.Trusted.RefuteQueries

namespace RelCertifier.Refute

open RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/refute_mutants/rover_terrain_6to12_m047/input.txt` (do not edit). -/
def rover_terrain_6to12_m047_IRm : PProblem :=
  {
    name := "rover_terrain_6to12"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "w", "zs", "u", "zh", "vz", "gamma", "theta_p", "ax", "phs", "omega_phs"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p")))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.1") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.25") (.var "u")))),
            ("zh", (.bin "-" (.var "vz") (.var "zh"))),
            ("vz", (.bin "-" (.bin "*" (.num "0.5") (.var "v")) (.var "vz"))),
            ("gamma", (.num "0")),
            ("theta_p", (.bin "*" (.bin "*" (.num "2") (.var "v")) (.bin "-" (.var "gamma") (.var "theta_p")))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p"))) (.var "ax")))),
            ("phs", (.bin "-" (.var "omega_phs") (.var "phs"))),
            ("omega_phs", (.bin "-" (.bin "*" (.num "0.05") (.var "ax")) (.var "omega_phs")))]
          guard := (.and (.and (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0"))) (.cmp "<=" (.var "u") (.num "0.25"))) (.cmp ">=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.02")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p")))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.03") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.45") (.var "u")))),
            ("zh", (.bin "-" (.var "vz") (.var "zh"))),
            ("vz", (.bin "-" (.bin "*" (.num "0.2") (.var "v")) (.var "vz"))),
            ("gamma", (.bin "*" (.bin "*" (.num "-0.5") (.var "v")) (.var "gamma"))),
            ("theta_p", (.bin "*" (.bin "*" (.num "2") (.var "v")) (.bin "-" (.var "gamma") (.var "theta_p")))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p"))) (.var "ax")))),
            ("phs", (.bin "-" (.var "omega_phs") (.var "phs"))),
            ("omega_phs", (.bin "-" (.bin "*" (.num "0.05") (.var "ax")) (.var "omega_phs")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0"))) (.cmp "<=" (.var "u") (.num "0.45")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p")))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.0") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.7") (.var "u")))),
            ("zh", (.bin "-" (.var "vz") (.var "zh"))),
            ("vz", (.bin "-" (.bin "*" (.num "0.05") (.var "v")) (.var "vz"))),
            ("gamma", (.bin "*" (.bin "*" (.num "-0.5") (.var "v")) (.var "gamma"))),
            ("theta_p", (.bin "*" (.bin "*" (.num "2") (.var "v")) (.bin "-" (.var "gamma") (.var "theta_p")))),
            ("ax", (.bin "*" (.num "5") (.bin "-" (.bin "-" (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs")) (.bin "*" (.num "9.81") (.var "theta_p"))) (.var "ax")))),
            ("phs", (.bin "-" (.var "omega_phs") (.var "phs"))),
            ("omega_phs", (.bin "-" (.bin "*" (.num "0.05") (.var "ax")) (.var "omega_phs")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "12.0")) (.cmp "<=" (.var "u") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["PAVED"] } ] }
    R := {
      stateVars := ["v", "s", "w", "zs", "u", "zh", "vz", "gamma", "theta_p", "ax", "phs", "omega_phs"]
      epsilon := "1.0"
      modes := [
        {
          name := "MUD"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "2.5") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.4") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.1") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.25") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.5") (.var "v")) (.var "zh"))),
            ("vz", (.num "0")),
            ("gamma", (.num "0")),
            ("theta_p", (.num "0")),
            ("ax", (.num "0")),
            ("phs", (.num "0")),
            ("omega_phs", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "5.0"))) (.cmp "<=" (.var "u") (.num "0.25")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["GRAVEL", "MUD"] },
        {
          name := "GRAVEL"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "4.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.15") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.03") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.45") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.2") (.var "v")) (.var "zh"))),
            ("vz", (.num "0")),
            ("gamma", (.num "0")),
            ("theta_p", (.num "0")),
            ("ax", (.num "0")),
            ("phs", (.num "0")),
            ("omega_phs", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "5.0")) (.cmp "<" (.var "s") (.num "12.0"))) (.cmp "<=" (.var "u") (.num "0.45")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["PAVED", "GRAVEL"] },
        {
          name := "PAVED"
          odes := [("v", (.bin "-" (.bin "-" (.bin "*" (.num "8.0") (.bin "-" (.var "w") (.var "v"))) (.bin "*" (.num "0.05") (.var "v"))) (.var "zs"))),
            ("s", (.var "v")),
            ("w", (.bin "*" (.num "3") (.bin "-" (.var "u") (.var "w")))),
            ("zs", (.bin "*" (.num "2") (.bin "-" (.num "0.0") (.var "zs")))),
            ("u", (.bin "*" (.num "4") (.bin "-" (.num "0.7") (.var "u")))),
            ("zh", (.bin "-" (.bin "*" (.num "0.05") (.var "v")) (.var "zh"))),
            ("vz", (.num "0")),
            ("gamma", (.num "0")),
            ("theta_p", (.num "0")),
            ("ax", (.num "0")),
            ("phs", (.num "0")),
            ("omega_phs", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "12.0")) (.cmp "<=" (.var "u") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "w") (.num "0.15"))) (.cmp "<=" (.var "w") (.num "0.8"))) (.cmp ">=" (.var "zs") (.num "0.0"))) (.cmp "<=" (.var "zs") (.num "0.12"))) (.cmp ">=" (.var "u") (.num "0.15"))) (.cmp "<=" (.var "u") (.num "0.8"))) (.cmp ">=" (.var "zh") (.num "0.0"))) (.cmp "<=" (.var "zh") (.num "0.5"))) (.cmp ">=" (.var "vz") (.num "0.0"))) (.cmp "<=" (.var "vz") (.num "0.5"))) (.cmp ">=" (.var "gamma") (.num "0.0"))) (.cmp "<=" (.var "gamma") (.num "0.02"))) (.cmp ">=" (.var "theta_p") (.num "0.0"))) (.cmp "<=" (.var "theta_p") (.num "0.02"))) (.cmp ">=" (.var "ax") (.num "-6.5"))) (.cmp "<=" (.var "ax") (.num "6.5"))) (.cmp ">=" (.var "phs") (.num "-0.65"))) (.cmp "<=" (.var "phs") (.num "0.65"))) (.cmp ">=" (.var "omega_phs") (.num "-0.65"))) (.cmp "<=" (.var "omega_phs") (.num "0.65")))
          next := ["PAVED"] } ] }
    invariants := [
      ("MUD", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15"))) (.cmp "<=" (.bin "+" (.var "L_theta_p") (.var "L_phs")) (.num "0.15"))) (.cmp "<=" (.var "L_vz") (.num "0.15"))) (.cmp "<=" (.var "L_ax") (.num "2.0"))) (.cmp "<=" (.var "R_omega_phs") (.num "0.1")))),
      ("GRAVEL", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15"))) (.cmp "<=" (.bin "+" (.var "L_theta_p") (.var "L_phs")) (.num "0.15"))) (.cmp "<=" (.var "L_vz") (.num "0.15"))) (.cmp "<=" (.var "L_ax") (.num "2.0"))) (.cmp "<=" (.var "R_omega_phs") (.num "0.1")))),
      ("PAVED", (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_u") (.var "R_u"))) (.cmp "<=" (.var "L_w") (.var "R_w"))) (.cmp "<=" (.var "R_zs") (.var "L_zs"))) (.cmp "<=" (.var "L_v") (.var "L_w"))) (.cmp "<=" (.var "L_w") (.var "L_u"))) (.cmp "<=" (.var "L_w") (.bin "+" (.var "L_v") (.num "0.25")))) (.cmp "<=" (.var "L_zh") (.num "0.15"))) (.cmp "<=" (.bin "+" (.var "L_theta_p") (.var "L_phs")) (.num "0.15"))) (.cmp "<=" (.var "L_vz") (.num "0.15"))) (.cmp "<=" (.var "L_ax") (.num "2.0"))) (.cmp "<=" (.var "R_omega_phs") (.num "0.1"))))] }

/-- The finder's witness (kind B). -/
def rover_terrain_6to12_m047_wit : RefWitE :=
  { kind := "B", u := 1, m := 1, q0 := 1, k := 9,
    wL := [(1/4 : ℚ), (6 : ℚ), (3/8 : ℚ), (1/16 : ℚ), (7/16 : ℚ), (1/8 : ℚ), (1/8 : ℚ), (1/64 : ℚ), (3/320 : ℚ), (0 : ℚ), (9/64 : ℚ), (1/2 : ℚ), (0 : ℚ)],
    wR := [(1/2 : ℚ), (7 : ℚ), (1/2 : ℚ), (0 : ℚ), (57/128 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] }

end RelCertifier.Refute

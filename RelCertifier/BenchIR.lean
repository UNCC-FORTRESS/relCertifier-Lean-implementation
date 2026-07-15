/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Parser-emitted benchmark IR literals (GENERATED — do not edit)

Regenerate with `relcert --emit-ir <file> <defname>` (scripts/gen via the transcription
tooling). The runtime battery re-parses each file and compares against these literals
with the derived `DecidableEq` (drift check); the `Faithful` certificates check the Lean
instances against them in the kernel.
-/
import RelCertifier.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_chain_rung1/input.txt` (do not edit). -/
def arm_chain_rung1_IR : PProblem :=
  {
    name := "arm_chain_rung1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachFast"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachSlow", "ApproachFast"] },
        {
          name := "ApproachSlow"
          odes := [("theta", (.num "0.3"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "ApproachSlow"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachFast", "Return"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "Approach"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "Approach"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Approach", "Return"] } ] }
    invariants := [
      ("ApproachFast", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("ApproachSlow", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("Return", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_chain_rung2/input.txt` (do not edit). -/
def arm_chain_rung2_IR : PProblem :=
  {
    name := "arm_chain_rung2"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachB", "ApproachA"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachC", "ApproachB"] },
        {
          name := "ApproachC"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Hold", "ApproachC"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "0.95")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Hold"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachFast"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachSlow", "ApproachFast"] },
        {
          name := "ApproachSlow"
          odes := [("theta", (.num "0.3"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "ApproachSlow"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["ApproachSlow", "Return"] } ] }
    invariants := [
      ("ApproachA", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("ApproachB", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("ApproachC", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30")))),
      ("Hold", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.30"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_chain_rung3/input.txt` (do not edit). -/
def arm_chain_rung3_IR : PProblem :=
  {
    name := "arm_chain_rung3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.535"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachB", "ApproachA"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachC", "ApproachB"] },
        {
          name := "ApproachC"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachC"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_fidelity_high/input.txt` (do not edit). -/
def arm_fidelity_high_IR : PProblem :=
  {
    name := "arm_fidelity_high"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.535"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachB", "ApproachA"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachC", "ApproachB"] },
        {
          name := "ApproachC"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachC"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_fidelity_low/input.txt` (do not edit). -/
def arm_fidelity_low_IR : PProblem :=
  {
    name := "arm_fidelity_low"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.85")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.85"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "Approach"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "Approach"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Approach", "Return"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_fidelity_mid/input.txt` (do not edit). -/
def arm_fidelity_mid_IR : PProblem :=
  {
    name := "arm_fidelity_mid"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.535"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachFast"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachSlow", "ApproachFast"] },
        {
          name := "ApproachSlow"
          odes := [("theta", (.num "0.3"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachSlow"] },
        {
          name := "Hold"
          odes := [("theta", (.bin "*" (.num "0.5") (.bin "-" (.num "0.6") (.var "theta"))))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.25")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.25"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/arm_refinement/input.txt` (do not edit). -/
def arm_refinement_IR : PProblem :=
  {
    name := "arm_refinement"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.85")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.85"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "Approach"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "Approach"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Approach", "Return"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4"))))] }

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

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_gain_M1/input.txt` (do not edit). -/
def endurance_gain_M1_IR : PProblem :=
  {
    name := "endurance_gain_M1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45")))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "3.45"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_orderlift_1to2/input.txt` (do not edit). -/
def endurance_orderlift_1to2_IR : PProblem :=
  {
    name := "endurance_orderlift_1to2"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "4.80") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "8.00") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "10.40") (.bin "*" (.num "4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "FLAT", "STEEP"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.5")) (.cmp "<=" (.var "a") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3")))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "2") (.var "R_v"))) (.num "1.3"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/endurance_orderlift_2to3/input.txt` (do not edit). -/
def endurance_orderlift_2to3_IR : PProblem :=
  {
    name := "endurance_orderlift_2to3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a", "j"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "14.40") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "24.00") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.var "j")),
            ("j", (.bin "-" (.bin "-" (.bin "-" (.num "31.20") (.bin "*" (.num "48") (.var "v"))) (.bin "*" (.num "16") (.var "a"))) (.bin "*" (.num "4") (.var "j"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.67")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.6")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.3"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "a", "j"]
      epsilon := "0.5"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "4.80") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.40")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "8.00") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.40")) (.cmp "<" (.var "v") (.num "0.575")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["STEEP", "FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "-" (.var "a") (.bin "*" (.num "4") (.var "v")))),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "10.40") (.bin "*" (.num "4") (.var "a")))),
            ("j", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.575")) (.cmp "<" (.var "v") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "2.8"))) (.cmp ">=" (.var "j") (.num "-1.6"))) (.cmp "<=" (.var "j") (.num "1.4"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.85")))
          next := ["MODER", "FLAT", "STEEP"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411"))))),
      ("MODER", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411"))))),
      ("FLAT", (.and (.cmp "<=" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "+" (.bin "-" (.bin "*" (.num "48") (.var "L_s")) (.bin "*" (.num "48") (.var "R_s"))) (.bin "*" (.num "16") (.var "L_v"))) (.bin "*" (.num "12") (.var "R_v"))) (.bin "*" (.num "4") (.var "L_a"))) (.bin "*" (.num "3") (.var "R_a"))) (.var "L_j")) (.num "1.9")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.411")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/match_multi_eps/input.txt` (do not edit). -/
def match_multi_eps_IR : PProblem :=
  {
    name := "match_multi_eps"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "1.5") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.05")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["ACCEL", "COAST"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["ACCEL", "COAST"] } ] }
    invariants := [
      ("ACCEL", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5")))),
      ("COAST", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/match_multi_rate/input.txt` (do not edit). -/
def match_multi_rate_IR : PProblem :=
  {
    name := "match_multi_rate"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "FAST"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.2")) (.cmp "<" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["MEDIUM", "FAST"] },
        {
          name := "MEDIUM"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.5")) (.cmp "<" (.var "v") (.num "0.7")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["SLOW", "MEDIUM"] },
        {
          name := "SLOW"
          odes := [("v", (.bin "*" (.num "1") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.7")) (.cmp "<=" (.var "v") (.num "0.95")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["RESET", "SLOW"] },
        {
          name := "RESET"
          odes := [("v", (.bin "*" (.num "4") (.bin "-" (.num "0.1") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.95")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["FAST", "RESET"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "DRIVE"
          odes := [("v", (.bin "*" (.num "1") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.2")) (.cmp "<=" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["DRIVE"] } ] }
    invariants := [
      ("FAST", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("MEDIUM", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("SLOW", (.cmp "<=" (.var "L_v") (.var "R_v"))),
      ("RESET", (.cmp "<=" (.var "L_v") (.var "R_v")))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/plant_fan_high/input.txt` (do not edit). -/
def plant_fan_high_IR : PProblem :=
  {
    name := "plant_fan_high"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.535"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachA"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachB", "ApproachA"] },
        {
          name := "ApproachB"
          odes := [("theta", (.num "0.35"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.5")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachC", "ApproachB"] },
        {
          name := "ApproachC"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachC"] },
        {
          name := "Hold"
          odes := [("theta", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.15"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/plant_fan_low/input.txt` (do not edit). -/
def plant_fan_low_IR : PProblem :=
  {
    name := "plant_fan_low"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.85")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-2") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.85"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "1.0"))) (.cmp ">=" (.var "v") (.num "-1.0"))) (.cmp "<=" (.var "v") (.num "1.0")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "Approach"
          odes := [("theta", (.num "0.2"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.7")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Return", "Approach"] },
        {
          name := "Return"
          odes := [("theta", (.bin "-" (.num "0") (.num "0.2")))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.70")) (.cmp "<" (.var "theta") (.num "0.85")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.0")))
          next := ["Approach", "Return"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.4"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/plant_fan_mid/input.txt` (do not edit). -/
def plant_fan_mid_IR : PProblem :=
  {
    name := "plant_fan_mid"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["theta", "v"]
      epsilon := "1.0"
      modes := [
        {
          name := "Accelerate"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<" (.var "theta") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<" (.var "v") (.num "0.355")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Brake", "Accelerate"] },
        {
          name := "Brake"
          odes := [("theta", (.var "v")),
            ("v", (.bin "+" (.bin "*" (.num "-1") (.bin "-" (.var "theta") (.num "0.5"))) (.bin "*" (.num "-1.0") (.var "v"))))]
          guard := (.and (.and (.cmp ">=" (.var "theta") (.num "0.5")) (.cmp "<=" (.var "theta") (.num "0.535"))) (.cmp "<=" (.var "v") (.num "0.0")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "theta") (.num "-0.05")) (.cmp "<=" (.var "theta") (.num "0.65"))) (.cmp ">=" (.var "v") (.num "-0.45"))) (.cmp "<=" (.var "v") (.num "0.45")))
          next := ["Accelerate", "Brake"] } ] }
    R := {
      stateVars := ["theta"]
      epsilon := "1.0"
      modes := [
        {
          name := "ApproachFast"
          odes := [("theta", (.num "0.5"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "0.35")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["ApproachSlow", "ApproachFast"] },
        {
          name := "ApproachSlow"
          odes := [("theta", (.num "0.3"))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.35")) (.cmp "<=" (.var "theta") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold", "ApproachSlow"] },
        {
          name := "Hold"
          odes := [("theta", (.bin "*" (.num "0.5") (.bin "-" (.num "0.6") (.var "theta"))))]
          guard := (.and (.cmp ">=" (.var "theta") (.num "0.6")) (.cmp "<" (.var "theta") (.num "1.15")))
          evolve := (.and (.cmp ">=" (.var "theta") (.num "0.0")) (.cmp "<=" (.var "theta") (.num "1.2")))
          next := ["Hold"] } ] }
    invariants := [
      ("Accelerate", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.3")))),
      ("Brake", (.cmp "<=" (.var "L_theta") (.bin "+" (.var "R_theta") (.num "0.3"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung1_2to3/input.txt` (do not edit). -/
def refinement_ladder_rover_rung1_2to3_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung1_2to3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung2_3to6/input.txt` (do not edit). -/
def refinement_ladder_rover_rung2_3to6_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung2_3to6"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi")))),
      ("MODER", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi")))),
      ("FLAT", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung2_6dof/input.txt` (do not edit). -/
def refinement_ladder_rover_rung2_6dof_IR : PProblem :=
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

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung2b_6dof/input.txt` (do not edit). -/
def refinement_ladder_rover_rung2b_6dof_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung2b_6dof"
    lambdaMin := "1.001"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0")),
            ("theta_p", (.num "0")),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0"))),
      ("MODER", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0"))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "-" (.bin "-" (.var "L_s") (.var "R_s")) (.num "0.2")) (.bin "*" (.bin "/" (.num "1") (.num "3")) (.bin "-" (.var "L_v") (.var "R_v")))) (.num "0")))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung2c_6dof/input.txt` (do not edit). -/
def refinement_ladder_rover_rung2c_6dof_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung2c_6dof"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("z", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("MODER", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("FLAT", (.and (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "R_v") (.var "L_v"))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "R_s") (.var "L_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung3_6to8/input.txt` (do not edit). -/
def refinement_ladder_rover_rung3_6to8_IR : PProblem :=
  {
    name := "refinement_ladder_rover_rung3_6to8"
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
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
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
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
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
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
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
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
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
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
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
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-0.5")) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "R_psi") (.var "R_psi")) (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))))) (.cmp "<=" (.bin "*" (.var "R_theta_p") (.var "R_theta_p")) (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_theta") (.var "L_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p"))))))),
      ("MODER", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "R_psi") (.var "R_psi")) (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))))) (.cmp "<=" (.bin "*" (.var "R_theta_p") (.var "R_theta_p")) (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_theta") (.var "L_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p"))))))),
      ("FLAT", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "R_psi") (.var "R_psi")) (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_psi") (.var "L_psi"))) (.bin "-" (.var "L_omega_psi") (.var "L_psi")))))) (.cmp "<=" (.bin "*" (.var "R_theta_p") (.var "R_theta_p")) (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.bin "*" (.num "3") (.bin "-" (.var "L_omega_theta") (.var "L_theta_p"))) (.bin "-" (.var "L_omega_theta") (.var "L_theta_p")))))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/refinement_ladder_rover_rung4_8to12/input.txt` (do not edit). -/
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

/-- Parser-emitted IR of `benchmarks/suite_uniform/robot_braking/input.txt` (do not edit). -/
def robot_braking_IR : PProblem :=
  {
    name := "robot_braking"
    lambdaMin := "1.0"
    lambdaMax := "3.0"
    L := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "CRUISE"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "1.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.8")) (.cmp "<=" (.var "v") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["CRUISE"] } ] }
    R := {
      stateVars := ["v"]
      epsilon := "2.0"
      modes := [
        {
          name := "FAST"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "0.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "3.5")) (.cmp "<" (.var "v") (.num "3.55")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["MID", "FAST"] },
        {
          name := "MID"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "0.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.5")) (.cmp "<=" (.var "v") (.num "3.5")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["SLOW", "MID"] },
        {
          name := "SLOW"
          odes := [("v", (.bin "*" (.num "0.5") (.bin "-" (.num "1.0") (.var "v"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "1.5")))
          evolve := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<=" (.var "v") (.num "3.65")))
          next := ["SLOW"] } ] }
    invariants := [
      ("CRUISE", (.cmp "<=" (.bin "-" (.var "L_v") (.var "R_v")) (.num "0.5")))] }

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

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_patrol_simple/input.txt` (do not edit). -/
def rover3tier_M1_IR : PProblem :=
  {
    name := "rover_patrol_simple"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "1.5") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.05")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "-0.05"))) (.cmp "<=" (.var "v") (.num "1.1")))
          next := ["ACCEL", "COAST"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.3"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.0") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.15")))
          next := ["ACCEL", "COAST"] } ] }
    invariants := [
      ("ACCEL", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5")))),
      ("COAST", (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover3tier_rung12/input.txt` (do not edit). -/
def rover3tier_rung12_IR : PProblem :=
  {
    name := "rover3tier_rung12"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "0.8") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.3")) (.cmp "<=" (.var "a") (.num "0.95"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.5")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "-0.3") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.3")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "-0.3")) (.cmp "<=" (.var "a") (.num "0.95"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.5")))
          next := ["ACCEL", "COAST"] } ] }
    R := {
      stateVars := ["v", "s", "a"]
      epsilon := "0.3"
      modes := [
        {
          name := "ACCEL"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.5")) (.cmp "<=" (.var "a") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0")))
          next := ["COAST", "ACCEL"] },
        {
          name := "COAST"
          odes := [("v", (.var "a")),
            ("s", (.var "v")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.cmp ">=" (.var "v") (.num "0.6"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.5")) (.cmp "<=" (.var "a") (.num "1.0"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0")))
          next := ["ACCEL", "COAST"] } ] }
    invariants := [
      ("ACCEL", (.and (.cmp "<=" (.var "L_v") (.bin "+" (.var "R_v") (.num "0.5"))) (.cmp "<=" (.var "L_a") (.bin "+" (.var "R_a") (.num "0.8"))))),
      ("COAST", (.cmp "<=" (.bin "+" (.bin "*" (.num "3") (.var "L_v")) (.var "L_a")) (.bin "+" (.bin "*" (.num "3") (.var "R_v")) (.num "1.2"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_4d_box/input.txt` (do not edit). -/
def rover_4d_box_IR : PProblem :=
  {
    name := "rover_4d_box"
    lambdaMin := "1.0"
    lambdaMax := "3.0"
    L := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "HOLD"
          odes := [("px", (.num "0")),
            ("py", (.num "0")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "9.0")) (.cmp "<=" (.var "px") (.num "11.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "9.0")) (.cmp "<=" (.var "px") (.num "11.1"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.1"))) (.cmp ">=" (.var "vx") (.num "0.0"))) (.cmp "<=" (.var "vx") (.num "2.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["HOLD"] } ] }
    R := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "APPROACH"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.bin "-" (.num "0.65") (.var "vx"))),
            ("vy", (.bin "-" (.num "0.0") (.var "vy")))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.7")) (.cmp "<=" (.var "vx") (.num "1.5")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "1.5"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["SETTLE", "APPROACH"] },
        {
          name := "SETTLE"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "0.7")))
          evolve := (.and (.and (.and (.cmp ">=" (.var "vx") (.num "0.5")) (.cmp "<=" (.var "vx") (.num "1.5"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["SETTLE"] } ] }
    invariants := [
      ("HOLD", (.cmp "<=" (.bin "-" (.var "L_px") (.var "R_px")) (.num "0.5")))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_attitude_cone_12dof/input.txt` (do not edit). -/
def rover_attitude_cone_12dof_IR : PProblem :=
  {
    name := "rover_attitude_cone_12dof"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "y", "e_lat", "omega_y"]
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
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.var "e_lat")),
            ("e_lat", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "e_lat")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.3"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.3"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.7"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.var "e_lat")),
            ("e_lat", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "e_lat")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.3"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.3"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.7"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "-" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "-" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "2") (.var "omega_theta")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "-" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "2") (.var "omega_phi")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.var "e_lat")),
            ("e_lat", (.var "omega_y")),
            ("omega_y", (.bin "-" (.bin "*" (.num "-1") (.var "e_lat")) (.bin "*" (.num "2") (.var "omega_y"))))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.3"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.3"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.7"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.7"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "y", "e_lat", "omega_y"]
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
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("e_lat", (.bin "*" (.num "-1") (.var "e_lat"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("e_lat", (.bin "*" (.num "-1") (.var "e_lat"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("y", (.bin "*" (.num "-1") (.var "y"))),
            ("e_lat", (.bin "*" (.num "-1") (.var "e_lat"))),
            ("omega_y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e_lat") (.num "-0.5")) (.cmp "<=" (.var "e_lat") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.3"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.3"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.5"))) (.cmp "<=" (.var "omega_y") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.7"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.7"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.5"))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.5")))),
      ("MODER", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.5"))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.5")))),
      ("FLAT", (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_psi") (.var "L_psi")) (.bin "*" (.var "L_omega_psi") (.var "L_omega_psi"))) (.num "0.5"))) (.cmp "<=" (.bin "+" (.bin "*" (.var "L_theta_p") (.var "L_theta_p")) (.bin "*" (.var "L_omega_theta") (.var "L_omega_theta"))) (.num "0.5"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_coupled/input.txt` (do not edit). -/
def rover_coupled_IR : PProblem :=
  {
    name := "rover_coupled"
    lambdaMin := "1.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.2")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "0.0")) (.cmp "<=" (.var "px") (.num "5.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Drift", "Drive"] },
        {
          name := "Drift"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.1")),
            ("vy", (.num "0.1"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "5.0")) (.cmp "<=" (.var "px") (.num "10.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Stop", "Drift"] },
        {
          name := "Stop"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.bin "*" (.num "-0.5") (.var "vx"))),
            ("vy", (.bin "*" (.num "-0.5") (.var "vy")))]
          guard := (.and (.cmp ">=" (.var "px") (.num "10.0")) (.cmp "<" (.var "px") (.num "10.75")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Stop"] } ] }
    R := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "Recover"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.4")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.25")) (.cmp "<=" (.var "vx") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Drive", "Recover"] },
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.2")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.3")) (.cmp "<" (.var "vx") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Safe", "Drive"] },
        {
          name := "Safe"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.75")) (.cmp "<=" (.var "vx") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Safe"] } ] }
    invariants := [
      ("Drive", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "0.5")))),
      ("Drift", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "1.0")))),
      ("Stop", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "2.0"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_dof_terrain_rung1/input.txt` (do not edit). -/
def rover_dof_terrain_rung1_IR : PProblem :=
  {
    name := "rover_dof_terrain_rung1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "psi") (.num "-0.5")) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_dof_terrain_rung2/input.txt` (do not edit). -/
def rover_dof_terrain_rung2_IR : PProblem :=
  {
    name := "rover_dof_terrain_rung2"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "z", "theta_p", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "z", "theta_p", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.num "0")),
            ("theta_p", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.num "0")),
            ("theta_p", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("z", (.num "0")),
            ("theta_p", (.num "0")),
            ("phi_r", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_dof_terrain_rung3/input.txt` (do not edit). -/
def rover_dof_terrain_rung3_IR : PProblem :=
  {
    name := "rover_dof_terrain_rung3"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "-2") (.var "omega_phi")))),
            ("z", (.var "vz")),
            ("vz", (.bin "*" (.num "-1") (.var "z"))),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "-2") (.var "omega_phi")))),
            ("z", (.var "vz")),
            ("vz", (.bin "*" (.num "-1") (.var "z"))),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("phi_r", (.var "omega_phi")),
            ("omega_phi", (.bin "+" (.bin "*" (.num "-1") (.var "phi_r")) (.bin "*" (.num "-2") (.var "omega_phi")))),
            ("z", (.var "vz")),
            ("vz", (.bin "*" (.num "-1") (.var "z"))),
            ("ax", (.num "0")),
            ("ay", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "ax") (.num "-1.0")) (.cmp "<=" (.var "ax") (.num "1.1"))) (.cmp ">=" (.var "ay") (.num "-1.0"))) (.cmp "<=" (.var "ay") (.num "1.1"))) (.cmp ">=" (.var "omega_phi") (.num "-1.0"))) (.cmp "<=" (.var "omega_phi") (.num "1.0"))) (.cmp ">=" (.var "omega_psi") (.num "-1.0"))) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "vz") (.num "-1.0"))) (.cmp "<=" (.var "vz") (.num "1.0"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "phi_r", "omega_phi", "z", "vz", "ax", "ay"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
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
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
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
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
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
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_dof_terrain_rung3_8d/input.txt` (do not edit). -/
def rover_dof_terrain_rung3_8d_IR : PProblem :=
  {
    name := "rover_dof_terrain_rung3_8d"
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
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.var "omega_psi")),
            ("omega_psi", (.bin "+" (.bin "*" (.num "-1") (.var "psi")) (.bin "*" (.num "-2") (.var "omega_psi")))),
            ("theta_p", (.var "omega_theta")),
            ("omega_theta", (.bin "+" (.bin "*" (.num "-1") (.var "theta_p")) (.bin "*" (.num "-2") (.var "omega_theta")))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<" (.var "s") (.num "899.95")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.0"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.0"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "omega_psi", "theta_p", "omega_theta", "z", "phi_r"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.var "v")),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_psi") (.num "-1.0")) (.cmp "<=" (.var "omega_psi") (.num "1.1"))) (.cmp ">=" (.var "omega_theta") (.num "-1.0"))) (.cmp "<=" (.var "omega_theta") (.num "1.1"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("MODER", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2"))))),
      ("FLAT", (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_drag/input.txt` (do not edit). -/
def rover_drag_IR : PProblem :=
  {
    name := "rover_drag"
    lambdaMin := "1.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("vx", (.bin "-" (.num "0.05") (.bin "*" (.num "0.3") (.bin "*" (.var "vx") (.var "vx")))))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.21")))
          evolve := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.4")))
          next := ["Cruise"] } ] }
    R := {
      stateVars := ["vx"]
      epsilon := "1.0"
      modes := [
        {
          name := "Track"
          odes := [("vx", (.bin "-" (.num "0.05") (.bin "*" (.num "0.3") (.bin "*" (.var "vx") (.var "vx")))))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.21")))
          evolve := (.and (.cmp ">=" (.var "vx") (.num "0.0")) (.cmp "<=" (.var "vx") (.num "1.4")))
          next := ["Track"] } ] }
    invariants := [
      ("Cruise", (.cmp "<=" (.bin "-" (.var "R_vx") (.var "L_vx")) (.num "0.05")))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_position/input.txt` (do not edit). -/
def rover_position_IR : PProblem :=
  {
    name := "rover_position"
    lambdaMin := "1.0"
    lambdaMax := "5.0"
    L := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.2")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "0.0")) (.cmp "<=" (.var "px") (.num "5.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Drift", "Drive"] },
        {
          name := "Drift"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.1")),
            ("vy", (.num "0.1"))]
          guard := (.and (.cmp ">=" (.var "px") (.num "5.0")) (.cmp "<=" (.var "px") (.num "10.0")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Stop", "Drift"] },
        {
          name := "Stop"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.bin "*" (.num "-0.5") (.var "vx"))),
            ("vy", (.bin "*" (.num "-0.5") (.var "vy")))]
          guard := (.and (.cmp ">=" (.var "px") (.num "10.0")) (.cmp "<" (.var "px") (.num "10.75")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp "<=" (.var "px") (.num "12.0"))) (.cmp ">=" (.var "py") (.num "-2.0"))) (.cmp "<=" (.var "py") (.num "2.0"))) (.cmp ">=" (.var "vx") (.num "-0.05"))) (.cmp "<=" (.var "vx") (.num "1.0"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.0")))
          next := ["Stop"] } ] }
    R := {
      stateVars := ["px", "py", "vx", "vy"]
      epsilon := "1.0"
      modes := [
        {
          name := "Recover"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.4")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.25")) (.cmp "<=" (.var "vx") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Drive", "Recover"] },
        {
          name := "Drive"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0.2")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.3")) (.cmp "<" (.var "vx") (.num "0.75")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Safe", "Drive"] },
        {
          name := "Safe"
          odes := [("px", (.var "vx")),
            ("py", (.var "vy")),
            ("vx", (.num "0")),
            ("vy", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "vx") (.num "0.75")) (.cmp "<=" (.var "vx") (.num "1.0")))
          evolve := (.and (.and (.and (.and (.cmp ">=" (.var "px") (.num "-0.05")) (.cmp ">=" (.var "vx") (.num "0.25"))) (.cmp "<=" (.var "vx") (.num "1.1"))) (.cmp ">=" (.var "vy") (.num "-1.0"))) (.cmp "<=" (.var "vy") (.num "1.1")))
          next := ["Safe"] } ] }
    invariants := [
      ("Drive", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "0.5")))),
      ("Drift", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "1.0")))),
      ("Stop", (.cmp "<=" (.var "L_px") (.bin "+" (.var "R_px") (.num "2.0"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_terrain_M1/input.txt` (do not edit). -/
def rover_terrain_M1_IR : PProblem :=
  {
    name := "rover_terrain_M1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["v", "s"]
      epsilon := "1.0"
      modes := [
        {
          name := "ROUGH"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.4") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "ROUGH"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.8") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["ROUGH", "SMOOTH", "FLAT"] },
        {
          name := "SMOOTH"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "1.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.25")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "SMOOTH"] } ] }
    R := {
      stateVars := ["v", "s"]
      epsilon := "0.5"
      modes := [
        {
          name := "ROUGH"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.4") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.0")) (.cmp "<" (.var "v") (.num "0.6")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "ROUGH"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "0.8") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.6")) (.cmp "<" (.var "v") (.num "1.0")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["ROUGH", "SMOOTH", "FLAT"] },
        {
          name := "SMOOTH"
          odes := [("v", (.bin "*" (.num "2") (.bin "-" (.num "1.2") (.var "v")))),
            ("s", (.var "v"))]
          guard := (.and (.cmp ">=" (.var "v") (.num "1.0")) (.cmp "<" (.var "v") (.num "1.25")))
          evolve := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "1.35")))
          next := ["FLAT", "SMOOTH"] } ] }
    invariants := [
      ("ROUGH", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2")))),
      ("FLAT", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2")))),
      ("SMOOTH", (.cmp "<=" (.bin "+" (.bin "*" (.num "6") (.var "L_s")) (.bin "*" (.num "2") (.var "L_v"))) (.bin "+" (.bin "+" (.bin "*" (.num "6") (.var "R_s")) (.bin "*" (.num "3") (.var "R_v"))) (.num "1.2"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/rover_tier_r1/input.txt` (do not edit). -/
def rover_tier_r1_IR : PProblem :=
  {
    name := "rover_tier_r1"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
    L := {
      stateVars := ["s", "v", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("s", (.var "v")),
            ("v", (.var "a")),
            ("a", (.bin "*" (.num "3") (.bin "-" (.num "0.4") (.var "a"))))]
          guard := (.and (.cmp ">=" (.var "v") (.num "0.3")) (.cmp "<=" (.var "v") (.num "1.21")))
          evolve := (.and (.and (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.0")) (.cmp "<=" (.var "a") (.num "0.55"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "100.0"))) (.cmp ">=" (.var "v") (.num "0.25"))) (.cmp "<=" (.var "v") (.num "1.4")))
          next := ["Cruise"] } ] }
    R := {
      stateVars := ["s", "v", "a"]
      epsilon := "1.0"
      modes := [
        {
          name := "Cruise"
          odes := [("s", (.var "v")),
            ("v", (.var "a")),
            ("a", (.bin "-" (.num "0") (.num "0")))]
          guard := (.cmp ">=" (.var "v") (.num "0.3"))
          evolve := (.and (.and (.and (.cmp ">=" (.var "a") (.num "0.3")) (.cmp "<=" (.var "a") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "v") (.num "0.25")))
          next := ["Cruise"] } ] }
    invariants := [
      ("Cruise", (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.5"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/story1_attdist_rung_a_6to8/input.txt` (do not edit). -/
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

/-- Parser-emitted IR of `benchmarks/suite_uniform/story1_attdist_rung_b_12dof/input.txt` (do not edit). -/
def story1_attdist_rung_b_12dof_IR : PProblem :=
  {
    name := "story1_attdist_rung_b_12dof"
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.4"))) (.cmp ">=" (.var "omega_psi") (.num "-0.4"))) (.cmp "<=" (.var "omega_psi") (.num "0.4"))) (.cmp ">=" (.var "omega_theta") (.num "-0.4"))) (.cmp "<=" (.var "omega_theta") (.num "0.4"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.4"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.4"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.5"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.0")))
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
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
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
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
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
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "omega_phi") (.num "-0.4")) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.6"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.6"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "omega_y") (.num "-0.4"))) (.cmp "<=" (.var "omega_y") (.num "0.5"))) (.cmp ">=" (.var "omega_z") (.num "-0.4"))) (.cmp "<=" (.var "omega_z") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.6"))) (.cmp "<=" (.var "psi") (.num "0.6"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.6"))) (.cmp "<=" (.var "theta_p") (.num "0.6"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-0.5"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.num "0.25"))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.num "0.25")))),
      ("MODER", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.num "0.25")))),
      ("FLAT", (.and (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_psi") (.var "R_psi"))) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")) (.bin "+" (.bin "-" (.var "L_omega_psi") (.var "R_omega_psi")) (.var "R_psi")))) (.num "0.25")) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "*" (.bin "*" (.num "2") (.bin "-" (.var "L_theta_p") (.var "R_theta_p"))) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.bin "*" (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")) (.bin "+" (.bin "-" (.var "L_omega_theta") (.var "R_omega_theta")) (.var "R_theta_p")))) (.num "0.25"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/story2_lateral_rung_a_8dof/input.txt` (do not edit). -/
def story2_lateral_rung_a_8dof_IR : PProblem :=
  {
    name := "story2_lateral_rung_a_8dof"
    lambdaMin := "1.0"
    lambdaMax := "8.0"
    L := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    R := {
      stateVars := ["v", "s", "psi", "theta_p", "y", "z", "phi_r", "w"]
      epsilon := "1.0"
      modes := [
        {
          name := "STEEP"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.30") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("y", (.bin "*" (.num "-1.0") (.var "y"))),
            ("z", (.bin "*" (.num "-1") (.var "z"))),
            ("phi_r", (.num "0")),
            ("w", (.bin "*" (.num "-1") (.var "w")))]
          guard := (.cmp ">=" (.var "s") (.num "1.4"))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "phi_r") (.num "-0.5")) (.cmp "<=" (.var "phi_r") (.num "0.6"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "w") (.num "-1.0"))) (.cmp "<=" (.var "w") (.num "0.15"))) (.cmp ">=" (.var "y") (.num "0.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("MODER", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p")))),
      ("FLAT", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_y") (.bin "+" (.var "R_y") (.num "0.3")))) (.cmp "<=" (.var "L_s") (.var "R_s"))) (.cmp "<=" (.var "L_psi") (.var "R_psi"))) (.cmp "<=" (.var "R_psi") (.var "L_psi"))) (.cmp "<=" (.var "L_theta_p") (.var "R_theta_p"))) (.cmp "<=" (.var "R_theta_p") (.var "L_theta_p"))))] }

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

/-- Parser-emitted IR of `benchmarks/suite_uniform/story3_rollover_base_12dof/input.txt` (do not edit). -/
def story3_rollover_base_12dof_IR : PProblem :=
  {
    name := "story3_rollover_base_12dof"
    lambdaMin := "1.0"
    lambdaMax := "6.0"
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
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
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "1.5"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.5"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.5"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.5"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.5"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.5"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.52"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp "<=" (.var "s") (.num "1000.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.5"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "0.15"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "0.15")))
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
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "L_v") (.var "L_r")) (.num "1.0"))) (.cmp "<=" (.num "0") (.bin "+" (.num "1.0") (.bin "*" (.var "L_v") (.var "L_r"))))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.var "L_r"))) (.bin "*" (.bin "*" (.num "0.156") (.var "L_r")) (.var "L_r"))) (.num "0.33")))),
      ("MODER", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "L_v") (.var "L_r")) (.num "1.0"))) (.cmp "<=" (.num "0") (.bin "+" (.num "1.0") (.bin "*" (.var "L_v") (.var "L_r"))))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.var "L_r"))) (.bin "*" (.bin "*" (.num "0.156") (.var "L_r")) (.var "L_r"))) (.num "0.33")))),
      ("FLAT", (.and (.and (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "*" (.var "L_v") (.var "L_r")) (.num "1.0"))) (.cmp "<=" (.num "0") (.bin "+" (.num "1.0") (.bin "*" (.var "L_v") (.var "L_r"))))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.var "L_r"))) (.bin "*" (.bin "*" (.num "0.156") (.var "L_r")) (.var "L_r"))) (.num "0.33"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/story3_rollover_ladder_rung_a/input.txt` (do not edit). -/
def story3_rollover_ladder_rung_a_IR : PProblem :=
  {
    name := "story3_rollover_ladder_rung_a"
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
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.0")) (.cmp "<" (.var "s") (.num "0.6"))) (.cmp "<=" (.var "v") (.num "0.3")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["MODER", "STEEP"] },
        {
          name := "MODER"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.50") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.and (.cmp ">=" (.var "s") (.num "0.6")) (.cmp "<" (.var "s") (.num "1.4"))) (.cmp "<=" (.var "v") (.num "0.5")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT", "MODER"] },
        {
          name := "FLAT"
          odes := [("v", (.bin "*" (.num "3") (.bin "-" (.num "0.65") (.var "v")))),
            ("s", (.bin "*" (.var "v") (.bin "-" (.bin "-" (.num "1") (.bin "*" (.num "0.5") (.bin "*" (.var "psi") (.var "psi")))) (.bin "*" (.num "0.3") (.bin "*" (.var "theta_p") (.var "theta_p")))))),
            ("psi", (.bin "*" (.num "-1") (.var "psi"))),
            ("omega_psi", (.num "0")),
            ("theta_p", (.bin "*" (.num "-1") (.var "theta_p"))),
            ("omega_theta", (.num "0")),
            ("e", (.bin "*" (.num "-1") (.var "e"))),
            ("r", (.num "0")),
            ("phi_r", (.bin "*" (.num "-1") (.var "phi_r"))),
            ("omega_phi", (.num "0")),
            ("z", (.num "0")),
            ("y", (.num "0"))]
          guard := (.and (.cmp ">=" (.var "s") (.num "1.4")) (.cmp "<=" (.var "v") (.num "0.65")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "e") (.num "-1.5")) (.cmp "<=" (.var "e") (.num "0.15"))) (.cmp ">=" (.var "omega_phi") (.num "-0.5"))) (.cmp "<=" (.var "omega_phi") (.num "0.6"))) (.cmp ">=" (.var "omega_psi") (.num "-0.5"))) (.cmp "<=" (.var "omega_psi") (.num "0.6"))) (.cmp ">=" (.var "omega_theta") (.num "-0.5"))) (.cmp "<=" (.var "omega_theta") (.num "0.6"))) (.cmp ">=" (.var "phi_r") (.num "-0.5"))) (.cmp "<=" (.var "phi_r") (.num "0.15"))) (.cmp ">=" (.var "psi") (.num "-0.5"))) (.cmp "<=" (.var "psi") (.num "0.15"))) (.cmp ">=" (.var "r") (.num "-1.52"))) (.cmp "<=" (.var "r") (.num "1.62"))) (.cmp ">=" (.var "s") (.num "0.0"))) (.cmp ">=" (.var "theta_p") (.num "-0.5"))) (.cmp "<=" (.var "theta_p") (.num "0.15"))) (.cmp ">=" (.var "v") (.num "0.0"))) (.cmp "<=" (.var "v") (.num "0.8"))) (.cmp ">=" (.var "y") (.num "-1.0"))) (.cmp "<=" (.var "y") (.num "1.1"))) (.cmp ">=" (.var "z") (.num "-1.0"))) (.cmp "<=" (.var "z") (.num "1.1")))
          next := ["FLAT"] } ] }
    invariants := [
      ("STEEP", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.bin "*" (.bin "*" (.num "0.156") (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e")))) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.num "0.33")))),
      ("MODER", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.bin "*" (.bin "*" (.num "0.156") (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e")))) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.num "0.33")))),
      ("FLAT", (.and (.and (.cmp "<=" (.var "L_v") (.var "R_v")) (.cmp "<=" (.var "L_s") (.bin "+" (.var "R_s") (.num "0.2")))) (.cmp "<=" (.bin "+" (.bin "+" (.bin "*" (.bin "*" (.num "1.125") (.var "L_e")) (.var "L_e")) (.bin "*" (.bin "*" (.num "0.25") (.var "L_e")) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.bin "*" (.bin "*" (.num "0.156") (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e")))) (.bin "-" (.var "L_r") (.bin "*" (.num "2") (.var "L_e"))))) (.num "0.33"))))] }

/-- Parser-emitted IR of `benchmarks/suite_uniform/story3_rollover_ladder_rung_b/input.txt` (do not edit). -/
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

/-- Parser-emitted IR of `benchmarks/suite_uniform/watertank/input.txt` (do not edit). -/
def watertank_IR : PProblem :=
  {
    name := "watertank"
    lambdaMin := "1.0"
    lambdaMax := "10.0"
    L := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.6") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<" (.var "x") (.num "13.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "Low"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "13.0")) (.cmp "<" (.var "x") (.num "20.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.1") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "20.0")) (.cmp "<" (.var "x") (.num "22.45")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] } ] }
    R := {
      stateVars := ["x"]
      epsilon := "1.0"
      modes := [
        {
          name := "Low"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.5") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "0.0")) (.cmp "<" (.var "x") (.num "10.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "Low"] },
        {
          name := "Mid"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "1.0") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "10.0")) (.cmp "<" (.var "x") (.num "17.0")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["High", "Mid"] },
        {
          name := "High"
          odes := [("x", (.bin "*" (.num "3") (.bin "-" (.num "0.1") (.bin "*" (.var "x") (.num "0.04")))))]
          guard := (.and (.cmp ">=" (.var "x") (.num "17.0")) (.cmp "<" (.var "x") (.num "22.45")))
          evolve := (.and (.cmp ">=" (.var "x") (.num "-0.05")) (.cmp "<=" (.var "x") (.num "25.0")))
          next := ["Mid", "High"] } ] }
    invariants := [
      ("Low", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3")))),
      ("Mid", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3")))),
      ("High", (.cmp "<=" (.var "L_x") (.bin "+" (.var "R_x") (.num "3"))))] }

/-- All emitted IR literals, keyed by benchmark directory (for the runtime drift check). -/
def benchIRTable : List (String × PProblem) := [
  ("arm_chain_rung1", arm_chain_rung1_IR),
  ("arm_chain_rung2", arm_chain_rung2_IR),
  ("arm_chain_rung3", arm_chain_rung3_IR),
  ("arm_fidelity_high", arm_fidelity_high_IR),
  ("arm_fidelity_low", arm_fidelity_low_IR),
  ("arm_fidelity_mid", arm_fidelity_mid_IR),
  ("arm_refinement", arm_refinement_IR),
  ("attitude_rate", attitude_rate_IR),
  ("endurance_gain_M1", endurance_gain_M1_IR),
  ("endurance_orderlift_1to2", endurance_orderlift_1to2_IR),
  ("endurance_orderlift_2to3", endurance_orderlift_2to3_IR),
  ("match_multi_eps", match_multi_eps_IR),
  ("match_multi_rate", match_multi_rate_IR),
  ("plant_fan_high", plant_fan_high_IR),
  ("plant_fan_low", plant_fan_low_IR),
  ("plant_fan_mid", plant_fan_mid_IR),
  ("refinement_ladder_rover_rung1_2to3", refinement_ladder_rover_rung1_2to3_IR),
  ("refinement_ladder_rover_rung2_3to6", refinement_ladder_rover_rung2_3to6_IR),
  ("refinement_ladder_rover_rung2_6dof", refinement_ladder_rover_rung2_6dof_IR),
  ("refinement_ladder_rover_rung2b_6dof", refinement_ladder_rover_rung2b_6dof_IR),
  ("refinement_ladder_rover_rung2c_6dof", refinement_ladder_rover_rung2c_6dof_IR),
  ("refinement_ladder_rover_rung3_6to8", refinement_ladder_rover_rung3_6to8_IR),
  ("refinement_ladder_rover_rung4_8to12", refinement_ladder_rover_rung4_8to12_IR),
  ("robot_braking", robot_braking_IR),
  ("rover3_M1", rover3_M1_IR),
  ("rover3tier_M1", rover3tier_M1_IR),
  ("rover3tier_rung12", rover3tier_rung12_IR),
  ("rover_4d_box", rover_4d_box_IR),
  ("rover_attitude_cone_12dof", rover_attitude_cone_12dof_IR),
  ("rover_coupled", rover_coupled_IR),
  ("rover_dof_terrain_rung1", rover_dof_terrain_rung1_IR),
  ("rover_dof_terrain_rung2", rover_dof_terrain_rung2_IR),
  ("rover_dof_terrain_rung3_8d", rover_dof_terrain_rung3_8d_IR),
  ("rover_dof_terrain_rung3", rover_dof_terrain_rung3_IR),
  ("rover_drag", rover_drag_IR),
  ("rover_position", rover_position_IR),
  ("rover_terrain_M1", rover_terrain_M1_IR),
  ("rover_tier_r1", rover_tier_r1_IR),
  ("story1_attdist_rung_a_6to8", story1_attdist_rung_a_6to8_IR),
  ("story1_attdist_rung_b_12dof", story1_attdist_rung_b_12dof_IR),
  ("story2_lateral_rung_a_8dof", story2_lateral_rung_a_8dof_IR),
  ("story2_lateral_rung_b_12dof", story2_lateral_rung_b_12dof_IR),
  ("story3_rollover_base_12dof", story3_rollover_base_12dof_IR),
  ("story3_rollover_ladder_rung_a", story3_rollover_ladder_rung_a_IR),
  ("story3_rollover_ladder_rung_b", story3_rollover_ladder_rung_b_IR),
  ("watertank", watertank_IR) ]


end RelCertifier.Parse

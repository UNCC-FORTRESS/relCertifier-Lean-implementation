/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py h2_refuel_ambientbias`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/h2_refuel_ambientbias/input.txt` (do not edit). -/
def h2_refuel_ambientbias_IRv2 : PProblem :=
  {
    name := "h2_refuel_ambientbias"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STAGE1"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "20") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "0.5")) (.cmp "<" (.var "p") (.num "18.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE1", "STAGE2", "ABORT"] },
        {
          name := "STAGE2"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "40") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "18.0")) (.cmp "<" (.var "p") (.num "38.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE2", "STAGE3", "ABORT"] },
        {
          name := "STAGE3"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "60") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "38.0")) (.cmp "<" (.var "p") (.num "58.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE3", "TOPOFF"] },
        {
          name := "TOPOFF"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "72.9") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "58.0")) (.cmp "<" (.var "p") (.num "72.4")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["TOPOFF", "COMPLETE"] },
        {
          name := "COMPLETE"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp ">=" (.var "p") (.num "72.4"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["COMPLETE"] },
        {
          name := "ABORT"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp "<" (.var "p") (.num "0.5"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["ABORT"] } ] }
    R := {
      stateVars := ["p"]
      epsilon := "1.0"
      modes := [
        {
          name := "STAGE1"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "20") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "0.5")) (.cmp "<" (.var "p") (.num "18.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE1", "STAGE2", "ABORT"] },
        {
          name := "STAGE2"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "40") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "18.0")) (.cmp "<" (.var "p") (.num "38.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE2", "STAGE3", "ABORT"] },
        {
          name := "STAGE3"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "60") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "38.0")) (.cmp "<" (.var "p") (.num "58.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["STAGE3", "TOPOFF"] },
        {
          name := "TOPOFF"
          odes := [("p", (.bin "*" (.num "0.05") (.bin "-" (.num "70.5") (.var "p"))))]
          guard := (.and (.cmp ">=" (.var "p") (.num "58.0")) (.cmp "<" (.var "p") (.num "70.0")))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["TOPOFF", "COMPLETE"] },
        {
          name := "COMPLETE"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp ">=" (.var "p") (.num "70.0"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["COMPLETE"] },
        {
          name := "ABORT"
          odes := [("p", (.num "0.0"))]
          guard := (.cmp "<" (.var "p") (.num "0.5"))
          evolve := (.and (.cmp ">=" (.var "p") (.num "0.0")) (.cmp "<=" (.var "p") (.num "87.5")))
          next := ["ABORT"] } ] }
    invariants := [
      ("STAGE1", (.cmp "<=" (.var "L_p") (.var "R_p"))),
      ("STAGE2", (.cmp "<=" (.var "L_p") (.var "R_p"))),
      ("STAGE3", (.cmp "<=" (.var "L_p") (.var "R_p"))),
      ("TOPOFF", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "2.9")))),
      ("COMPLETE", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "2.9")))),
      ("ABORT", (.cmp "<=" (.var "L_p") (.bin "+" (.var "R_p") (.num "2.9"))))] }

end RelCertifier.Parse

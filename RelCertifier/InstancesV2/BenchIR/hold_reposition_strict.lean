/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hold_reposition_strict` (prelanding_demo) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_prelanding_demo.py`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/prelanding_demo/hold_reposition_strict/input.txt` (do not edit). -/
def hold_reposition_strict_IRv2 : PProblem :=
  {
    name := "hold_reposition_strict"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["y"]
      epsilon := "1.0"
      modes := [
        {
          name := "Hold"
          odes := [("y", (.num "0.0"))]
          guard := (.cmp ">=" (.var "y") (.num "-10.0"))
          evolve := (.cmp ">=" (.var "y") (.num "-10.0"))
          next := ["Hold"] } ] }
    R := {
      stateVars := ["y"]
      epsilon := "1.0"
      modes := [
        {
          name := "Up"
          odes := [("y", (.num "1.0"))]
          guard := (.cmp "<=" (.var "y") (.num "0.0"))
          evolve := (.cmp ">=" (.var "y") (.num "-10.0"))
          next := ["Up", "Hold"] },
        {
          name := "Hold"
          odes := [("y", (.num "0.0"))]
          guard := (.cmp ">=" (.var "y") (.num "0.0"))
          evolve := (.cmp ">=" (.var "y") (.num "-10.0"))
          next := ["Hold"] } ] }
    invariants := [
      ("Hold", (.and (.cmp "<" (.var "L_y") (.bin "+" (.var "R_y") (.num "5.0"))) (.cmp "<=" (.var "R_y") (.num "0.0"))))]
    prelanding := true }

end RelCertifier.Parse

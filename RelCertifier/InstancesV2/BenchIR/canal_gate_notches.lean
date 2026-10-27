/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `canal_gate_notches` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py canal_gate_notches`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/canal_gate_notches/input.txt` (do not edit). -/
def canal_gate_notches_IRv2 : PProblem :=
  {
    name := "canal_gate_notches"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["h"]
      epsilon := "10.0"
      modes := [
        {
          name := "RAISE"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.95") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<" (.var "h") (.num "0.4")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["RAISE", "HOLD"] },
        {
          name := "HOLD"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.65") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.4")) (.cmp "<" (.var "h") (.num "0.9")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["RAISE", "HOLD", "LOWER"] },
        {
          name := "LOWER"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.3") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.9")) (.cmp "<=" (.var "h") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["HOLD", "LOWER"] } ] }
    R := {
      stateVars := ["h"]
      epsilon := "10.0"
      modes := [
        {
          name := "N100"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "1") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<" (.var "h") (.num "0.6")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["N100", "N75", "N50", "N25"] },
        {
          name := "N75"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.75") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["N100", "N75", "N50", "N25"] },
        {
          name := "N50"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.5") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["N100", "N75", "N50", "N25"] },
        {
          name := "N25"
          odes := [("h", (.bin "*" (.num "0.006") (.bin "-" (.num "0.25") (.var "h"))))]
          guard := (.and (.cmp ">=" (.var "h") (.num "0.7")) (.cmp "<=" (.var "h") (.num "1.2")))
          evolve := (.and (.cmp ">=" (.var "h") (.num "0.0")) (.cmp "<=" (.var "h") (.num "1.2")))
          next := ["N100", "N75", "N50", "N25"] } ] }
    invariants := [
      ("RAISE", (.and (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.15"))) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.15"))))),
      ("HOLD", (.and (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.15"))) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.15"))))),
      ("LOWER", (.and (.cmp "<=" (.var "L_h") (.bin "+" (.var "R_h") (.num "0.15"))) (.cmp "<=" (.var "R_h") (.bin "+" (.var "L_h") (.num "0.15")))))] }

end RelCertifier.Parse

/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `syringe_relay_prearm` (suite_v2) — parser-emitted IR literal (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py syringe_relay_prearm`.
-/
import RelCertifier.Trusted.Parse

namespace RelCertifier.Parse

/-- Parser-emitted IR of `benchmarks/suite_v2/syringe_relay_prearm/input.txt` (do not edit). -/
def syringe_relay_prearm_IRv2 : PProblem :=
  {
    name := "syringe_relay_prearm"
    lambdaMin := "1.0"
    lambdaMax := "1.0"
    L := {
      stateVars := ["v1", "v2", "C", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "RUN1"
          odes := [("v1", (.num "0.05")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "v1") (.num "45.0")) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["RUN1", "PREARM", "READY"] },
        {
          name := "PREARM"
          odes := [("v1", (.num "0.05")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.09"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "45.0")) (.cmp "<" (.var "v1") (.num "49.5"))) (.cmp "<" (.var "b") (.num "1.0"))) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["PREARM", "READY", "TAKEUP2"] },
        {
          name := "READY"
          odes := [("v1", (.num "0.05")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "45.0")) (.cmp "<" (.var "v1") (.num "49.5"))) (.cmp ">=" (.var "b") (.num "1.0"))) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["READY", "RUN2"] },
        {
          name := "TAKEUP2"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.neg (.num "0.29")) (.var "C"))),
            ("b", (.num "0.09"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp "<" (.var "b") (.num "1.0"))) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["TAKEUP2", "RUN2"] },
        {
          name := "RUN2"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.05")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp ">=" (.var "b") (.num "1.0"))) (.cmp "<" (.var "v2") (.num "49.5"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["RUN2", "END"] },
        {
          name := "END"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.neg (.num "0.29")) (.var "C"))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp ">=" (.var "v2") (.num "49.5"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["END"] } ] }
    R := {
      stateVars := ["v1", "v2", "C", "b"]
      epsilon := "0.1"
      modes := [
        {
          name := "RUN1"
          odes := [("v1", (.num "0.05")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp "<" (.var "v1") (.num "49.5")) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["RUN1", "TAKEUP2", "RUN2"] },
        {
          name := "TAKEUP2"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.neg (.num "0.29")) (.var "C"))),
            ("b", (.num "0.09"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp "<" (.var "b") (.num "1.0"))) (.cmp "<=" (.var "v2") (.num "0.0"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["TAKEUP2", "RUN2"] },
        {
          name := "RUN2"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.05")),
            ("C", (.bin "*" (.num "0.29") (.bin "-" (.num "1.0") (.var "C")))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp ">=" (.var "b") (.num "1.0"))) (.cmp "<" (.var "v2") (.num "49.5"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["RUN2", "END"] },
        {
          name := "END"
          odes := [("v1", (.num "0.0")),
            ("v2", (.num "0.0")),
            ("C", (.bin "*" (.neg (.num "0.29")) (.var "C"))),
            ("b", (.num "0.0"))]
          guard := (.and (.and (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "49.5")) (.cmp ">=" (.var "v2") (.num "49.5"))) (.cmp ">=" (.var "v1") (.num "0.0"))) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          evolve := (.and (.and (.and (.and (.and (.and (.and (.cmp ">=" (.var "v1") (.num "0.0")) (.cmp "<=" (.var "v1") (.num "50.0"))) (.cmp ">=" (.var "v2") (.num "0.0"))) (.cmp "<=" (.var "v2") (.num "50.0"))) (.cmp ">=" (.var "C") (.num "0.0"))) (.cmp "<=" (.var "C") (.num "1.0"))) (.cmp ">=" (.var "b") (.num "0.0"))) (.cmp "<=" (.var "b") (.num "1.2")))
          next := ["END"] } ] }
    invariants := [
      ("RUN1", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "L_C") (.var "R_C"))) (.cmp "<=" (.var "R_C") (.var "L_C"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("PREARM", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "L_C") (.var "R_C"))) (.cmp "<=" (.var "R_C") (.var "L_C"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("READY", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "L_C") (.var "R_C"))) (.cmp "<=" (.var "R_C") (.var "L_C"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("TAKEUP2", (.and (.and (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "L_C") (.var "R_C"))) (.cmp "<=" (.var "R_C") (.var "L_C"))) (.cmp "<=" (.var "R_b") (.var "L_b")))),
      ("RUN2", (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "R_C") (.var "L_C")))),
      ("END", (.and (.and (.and (.and (.cmp "<=" (.var "L_v1") (.var "R_v1")) (.cmp "<=" (.var "R_v1") (.var "L_v1"))) (.cmp "<=" (.var "L_v2") (.var "R_v2"))) (.cmp "<=" (.var "R_v2") (.var "L_v2"))) (.cmp "<=" (.var "R_C") (.var "L_C"))))] }

end RelCertifier.Parse

#!/usr/bin/env python3
"""Regenerate RelCertifier/Instances/BenchCoverReplay.lean from BenchCovers.lean."""
import re, os
os.chdir(os.path.join(os.path.dirname(__file__), ".."))
s = open("RelCertifier/Instances/BenchCovers.lean").read()
names = re.findall(r'def (\w+)_cover : CoverEmitE', s)
out = open("RelCertifier/Instances/BenchCoverReplay.lean", "w")
out.write("""/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Kernel replays of the tool's cover gate (R5 — generated, do not edit)

Per benchmark: for EVERY emitted left-mode cover and EVERY admissible start, the
verified `decideCovered` — on the SAME structural graph the tool built
(`buildCoverGraph` over the SAME emitted flags/successors/prunes, same fuel, same
budget, σ = preJ) — accepts, by kernel computation. This replays the tool's CERTIFIED
gate inside the kernel: three standard axioms, no Z3, no IO.

Regenerate: `scripts/gen_cover_replay.py`.
-/
import RelCertifier.Instances.BenchCovers
import RelCertifier.Checker.Checker
import RelCertifier.Instances.BenchIR
import RelCertifier.Trusted.Run

namespace RelCertifier

/-- The replay predicate: every window, every admissible start, checker accepts. -/
def coverReplays (p : Parse.PProblem) (c : CoverEmitE) : Bool :=
  c.covers.all (fun lc =>
    lc.admissible.all (fun q0 =>
      decideCovered (V := Var 1)
        (buildCoverGraph lc.flags (Run.succOf p)
          (fun a b => c.pruned.contains (a, b)))
        (coverFuel lc.flags lc.bBudget)
        ⟨nodeIdx lc.flags q0, lc.bBudget, SrcSetting.preJ⟩))

""")
for n in names:
    out.write(f"theorem {n}_cover_replay : coverReplays Parse.{n}_IR {n}_cover = true := by decide\n\n")
out.write("end RelCertifier\n")
print(f"wrote {len(names)} replays")

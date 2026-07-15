#!/usr/bin/env python3
"""Generate Instances/RealInstances.lean: per-benchmark real-model end-to-end theorems.

Data mined from FaithfulCerts.lean (family + IR/meta/model triples + meta literals),
the instance files (model dims + dtQ), and BenchIR.lean (R-side epsilon strings).
The time-unit value u = (eps_R/lam)/dtQ is mirrored here in exact integer arithmetic
(parseQ/qDiv/qMk semantics) to emit the per-benchmark rfl constant and positivity.
"""
import re, os, sys
from fractions import Fraction

root = os.path.join(os.path.dirname(__file__), "..")
fc = open(os.path.join(root, "RelCertifier/Instances/FaithfulCerts.lean")).read()
bench_ir = open(os.path.join(root, "RelCertifier/Instances/BenchIR.lean")).read()
inst = ""
for f in ["SettlingInstances", "TerrainInstances", "AffineInstances"]:
    inst += open(os.path.join(root, f"RelCertifier/Instances/{f}.lean")).read()

triples = re.findall(
    r'example : (faithfulSettling|faithfulTerrain|faithfulAffine) (\S+) (\S+) (\S+) = true := rfl', fc)

def parseQ(s):
    # mirror of Faithful.parseQ: returns (n, d) ints, d > 0
    neg = s.startswith("-")
    if neg: s = s[1:]
    if "." in s:
        w, f = s.split(".", 1)
        n = int(w) * (10 ** len(f)) + int(f)
        d = 10 ** len(f)
    else:
        n, d = int(s), 1
    return (-n if neg else n, d)

def qMk(n, d):
    return (-n, -d) if d < 0 else (n, d)

def qDiv(a, b):
    return qMk(a[0]*b[1], a[1]*b[0])

out = []
out.append("""/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# GENERATED per-benchmark real-model end-to-end theorems (scripts/gen_real_instances.py)

One theorem per benchmark: the generic family theorem instantiated at the parser-emitted
IR, the transcription metadata, and the kernel-certified model, with every decidable side
condition discharged. Residual hypotheses per theorem: the freshness data (mv/tg choices)
and the Z3 BoxLe certificates — the z3_unsat_sound leaf, exactly as in the watertank demo.
-/
import RelCertifier.Proofs.Transfer.RealEndToEnd
import RelCertifier.Instances.FaithfulCerts

namespace RelCertifier

open DL DLCalTiming DLRel Function Set RelCertifier.Parse

""")

PADDED = {"arm_chain_rung3", "arm_fidelity_high", "arm_fidelity_low", "arm_fidelity_mid",
          "arm_refinement", "plant_fan_high", "plant_fan_low", "plant_fan_mid"}
for fam, ir, meta, model in triples:
    bench = ir[:-3] if ir.endswith("_IR") else ir
    padded = bench in PADDED
    # meta literal: lam + scales
    mm = re.search(r'def '+re.escape(meta)+r'\s*:\s*TransMeta\s*:=\s*\{\s*lam := \(qMk (-?\d+) (-?\d+)\)', fc)
    lam = qMk(int(mm.group(1)), int(mm.group(2)))
    # model: n and dtQ. Terrain/affine: model is the T/A wrapper; find its core or dtQ inside.
    if fam == "faithfulSettling":
        md = re.search(r'def '+re.escape(model)+r'\s*:\s*SettlingModel (\d+)', inst)
        n = int(md.group(1))
        core_expr = model
    else:
        kind = "TerrainModel" if fam == "faithfulTerrain" else "AffineModel"
        md = re.search(r'def '+re.escape(model)+r'\s*:\s*'+kind+r' (\d+)', inst)
        n = int(md.group(1))
        core_expr = model + ".core"
    # dtQ: first "dtQ := k" after the model def (settling: in literal; T/A: in its core literal or named core)
    start = inst.index(f"def {model} ")
    seg = inst[start:start+6000]
    dq = re.search(r'dtQ := (-?\d+)', seg)
    if not dq:
        # named core reference: core := <name>
        cm = re.search(r'core := (\w+)', seg)
        cstart = inst.index(f"def {cm.group(1)} ")
        dq = re.search(r'dtQ := (-?\d+)', inst[cstart:cstart+6000])
    dtQ = int(dq.group(1))
    # epsilon: R-block of the IR literal
    istart = bench_ir.index(f"def {ir} ")
    ib = bench_ir[istart:bench_ir.index("\ndef ", istart+10) if "\ndef " in bench_ir[istart+10:] else len(bench_ir)]
    rblk = ib[ib.index("R := {"):]
    eps = re.search(r'epsilon := "([^"]+)"', rblk).group(1)
    epsq = parseQ(eps)
    u = qDiv(qDiv(epsq, lam), (dtQ, 1))
    assert u[0] > 0 and u[1] > 0, (bench, u)

    fam_thm = {"faithfulSettling": "settling_real_end_to_end",
               "faithfulTerrain": "terrain_real_end_to_end",
               "faithfulAffine": "affine_real_end_to_end"}[fam]
    gd_real = {"faithfulSettling": f"realGdOf {ir} {model}",
               "faithfulTerrain": f"realGdOfT {ir} {meta}.scales {model}",
               "faithfulAffine": f"realGdOfA {ir} {meta}.scales {model}"}[fam]
    graph = {"faithfulSettling": f"{model}.graph"}.get(fam, f"{core_expr}.graph")
    envF = {"faithfulSettling": f"{model}.envF"}.get(fam, f"{core_expr}.envF")
    gdOf = f"{model}.GdOf"
    modes = f"{model}.modes" if fam == "faithfulSettling" else f"{core_expr}.modes"
    dt = f"{model}.dt" if fam == "faithfulSettling" else f"{core_expr}.dt"
    wf = {"faithfulSettling": "decideWellFormed", "faithfulTerrain": "decideWellFormedT",
          "faithfulAffine": "decideWellFormedA"}[fam]
    dtq_expr = f"{model}.dtQ" if fam == "faithfulSettling" else f"{core_expr}.dtQ"

    if padded:
        out.append(f"""/-- `{bench}` (PADDED model): real-model end to end (residuals: freshness data only). -/
theorem {bench}_real
    (mv tg : Var {n}) (g : Term (Var {n})) (fL : Fin {n} → Term (Var {n}))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ ({gdOf} q').fv)
    (htgGd : ∀ q', tg ∉ ({gdOf} q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ ({gdOf} q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) :
    ∀ q pm m, {ir}.R.modes[q]? = some pm → {modes}[q]? = some m →
      GuardSettlingB {graph} ({gd_real})
        (realFieldOf {ir}.R.stateVars pm {n}) (Term.const 1)
        (realEnvOf {ir}.R.stateVars {n} pm)
        ((qDiv (qDiv (⟨{epsq[0]}, {epsq[1]}⟩ : QF) {meta}.lam) (qOfInt {dtq_expr})).val
          * (({dt} : ℤ) : ℝ)) q :=
  settling_real_end_to_end_pad {ir} {meta} {model}
    (εR := ⟨{epsq[0]}, {epsq[1]}⟩) rfl rfl
    (by decide) (by decide)
    (by intro j hj; interval_cases j <;> decide)
    (fun j hj => sigmaOf_pos_lt (by decide) hj)
    (by
      have h : qDiv (qDiv (⟨{epsq[0]}, {epsq[1]}⟩ : QF) {meta}.lam)
          (qOfInt {dtq_expr}) = (⟨{u[0]}, {u[1]}⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide) (by decide) (by decide) (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, {model}])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd

""")
        continue

    out.append(f"""/-- `{bench}`: real-model end to end (residuals: freshness data only — the conclusion is single-system; no Z3 hypotheses remain). -/
theorem {bench}_real
    (mv tg : Var {n}) (g : Term (Var {n})) (fL : Fin {n} → Term (Var {n}))
    (hg : mv ∉ g.fv)
    (hmvclk : mv ∉ (DLCalTiming.clk tg (leftBlock fL)).bound)
    (hmvtg : mv ≠ tg)
    (hmvGd : ∀ q', mv ∉ ({gdOf} q').fv)
    (htgGd : ∀ q', tg ∉ ({gdOf} q').fv)
    (hfrzGd : ∀ q', ∀ x ∈ ({gdOf} q').fv,
        x ∉ (DLCalTiming.clk tg (leftBlock fL)).bound) :
    ∀ q pm m, {ir}.R.modes[q]? = some pm → {modes}[q]? = some m →
      GuardSettlingB {graph} ({gd_real})
        (realFieldOf {ir}.R.stateVars pm {n}) (Term.const 1)
        (realEnvOf {ir}.R.stateVars {n} pm)
        ((qDiv (qDiv (⟨{epsq[0]}, {epsq[1]}⟩ : QF) {meta}.lam) (qOfInt {dtq_expr})).val
          * (({dt} : ℤ) : ℝ)) q :=
  {fam_thm} {ir} {meta} {model}
    (εR := ⟨{epsq[0]}, {epsq[1]}⟩) rfl rfl
    (by decide) rfl
    (by intro j hj; interval_cases j <;> decide)
    (fun j => sigmaOf_pos (by decide) (by decide) j)
    (by
      have h : qDiv (qDiv (⟨{epsq[0]}, {epsq[1]}⟩ : QF) {meta}.lam)
          (qOfInt {dtq_expr}) = (⟨{u[0]}, {u[1]}⟩ : QF) := rfl
      rw [h]
      norm_num [QF.val])
    (by decide)
    mv tg g fL rfl (by norm_num [SettlingModel.dt, {model}])
    hg hmvclk hmvtg hmvGd htgGd hfrzGd

""")

out.append("end RelCertifier\n")
open(os.path.join(root, "RelCertifier/Instances/RealInstances.lean"), "w").write("".join(out))
print(f"generated {len(triples)} instances ({len(PADDED)} padded)")

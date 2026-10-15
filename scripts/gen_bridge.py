#!/usr/bin/env python3
"""Emit the generic-bridge instances: RelCertifier/InstancesV2/Bridge/<Camel>.lean, one per
suite_v2 benchmark, and the aggregator RelCertifier/InstancesV2/Bridge.lean.

Each instance states Theorem 3 of its benchmark through the generic bridge
(`Proofs/Encoding/Emitted/`): the structural bundles decided in the kernel, Assumption 1
transported from the suite's `WellFormedR` lemma, the verdicts assumed as `Verdicts` (the
groups `relcert-bridge-verdicts` discharges). Benchmarks whose left modes declare one row take
the window form (`windowClaim`, two auxiliary coordinates); those with per-mode rows take the
mode-keyed form (`keyedClaim`, three).

Usage: python3 scripts/gen_bridge.py [bench ...]   (default: all of benchmarks/suite_v2)
"""
import os, re, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
SUITE = "benchmarks/suite_v2"
OUT = "RelCertifier/InstancesV2/Bridge"
WF_DIRS = [("RelCertifier/InstancesV2/WellFormed", "RelCertifier.InstancesV2.WellFormed"),
           ("RelCertifier/Instances/WellFormed", "RelCertifier.Instances.WellFormed")]

# benchmarks whose left modes declare distinct rows (the keyed form); every other benchmark's
# rows are identical (`rowsSame`, checked in the kernel by the window instance)
KEYED = {"acc_spoof_limp", "acc_tune_limp", "platoon3_linkloss", "platoon_delay_linkloss",
         "rover3tier_rung12", "rover_patrol_refine", "rover_patrol_zones",
         "sat3w_detumble_phases", "sat_detumble_phases", "story1_attdist_rung_a_6to8",
         "story1_attdist_rung_b_12dof", "story3_rollover_ladder_rung_b"}


def all_benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt"))

def camel(b):
    return "".join(w.capitalize() for w in b.split("_"))

def dims():
    """The bridge dimension of each benchmark: the pack table's `dim`."""
    src = open("RelCertifier/VerdictsV2/RunV2.lean").read()
    d = {}
    for m in re.finditer(r'⟨"(\w+)", (\d+), \d+, \[', src):
        d.setdefault(m.group(1), int(m.group(2)))
    return d

def wf_info(b):
    """The WellFormed leaf of `b`: module, namespace, graph and guard names."""
    for d, modbase in WF_DIRS:
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".lean"):
                continue
            src = open(f"{d}/{fn}").read()
            m = re.search(rf"theorem {b}_wellFormedR\s*:\s*WellFormedR (\w+) (\w+) \(epsR", src)
            if not m:
                continue
            ns = re.findall(r"^namespace (\w+)", src, re.M)
            ns = [x for x in ns if x != "RelCertifier"]
            return dict(module=f"{modbase}.{fn[:-5]}", ns=ns[-1], G=m.group(1), guard=m.group(2))
    return None

TEMPLATE = '''/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`{rows_doc}), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.{form_mod}
import RelCertifier.Proofs.Encoding.Emitted.Transport
import {wfmod}
import RelCertifier.InstancesV2.BenchCovers.{b}
import RelCertifier.InstancesV2.BenchProgress.{b}

namespace RelCertifier.Bridge.{camel}

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle

abbrev IR := Parse.{b}_IRv2
abbrev cX := Oracle.{b}_cutsV2X
abbrev cov := {b}_coverV2
abbrev prog := Progress.{b}_coverV2_progress

theorem struct_ok : structOK IR {n} cov cX = true := by decide +kernel
theorem prog_ok : progOK IR {n} cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR {n} cov = true := by decide +kernel
{rows_thm}theorem nR_eq : nR IR = {ns}.{G}.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR {ns}.{G} = true := by decide +kernel
theorem src_ok : edgesSrcOK IR {ns}.{G} = true := by decide +kernel

/-- Assumption 1, transported from `{ns}.{b}_wellFormedR`. -/
theorem wellFormedR : WellFormedR (grOf IR {n} (prunedOf cov)) (guardR IR {n}) (epsR IR) :=
  wellFormedR_transport {ns}.{b}_wellFormedR (by rw [grOf_len, nR_eq])
    (fun q m' hm' => by
      obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
      rw [nR_eq] at hq
      exact ⟨_, {ns}.{modeAt} q hq, rfl, rfl⟩)
    (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))

{claim}
end RelCertifier.Bridge.{camel}
'''

WINDOW_CLAIM = '''/-- **Theorem 3 of `{b}`** (window form): every verdict group of the benchmark `unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR {n} cX cov 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok wellFormedR rows_same 0 1
    (by decide) dt hdt
'''

KEYED_CLAIM = '''/-- **Theorem 3 of `{b}`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR {n} cX cov 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt
'''

def emit(b, n):
    info = wf_info(b)
    if info is None:
        # Assumption 1 holds only on a region for this benchmark (`WellFormedRIn`); the
        # unconditional form the general theorem takes is not available: not bridged
        print(f"  skipped {b}: no unconditional WellFormedR lemma")
        return False
    keyed = b in KEYED
    modeAt = f"{info['G']}_modeAt"
    rows_thm = "" if keyed else "theorem rows_same : rowsSame IR = true := by decide +kernel\n"
    claim = (KEYED_CLAIM if keyed else WINDOW_CLAIM).format(b=b, n=n)
    txt = TEMPLATE.format(b=b, camel=camel(b), n=n, form_mod="Keyed" if keyed else "Window",
                          wfmod=info["module"], ns=info["ns"], G=info["G"], modeAt=modeAt,
                          rows_doc="" if keyed else ", `rows_same`", rows_thm=rows_thm,
                          claim=claim)
    os.makedirs(OUT, exist_ok=True)
    with open(f"{OUT}/{camel(b)}.lean", "w") as f:
        f.write(txt)
    return True

def aggregator(benches):
    with open("RelCertifier/InstancesV2/Bridge.lean", "w") as f:
        f.write("/- The generic-bridge instances of suite_v2 (GENERATED by `scripts/gen_bridge.py`). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.Bridge.{camel(b)}\n")

def main():
    benches = all_benches()
    todo = sys.argv[1:] or benches
    d = dims()
    done = []
    for b in benches:
        n = d.get(b)
        if n is None:
            sys.exit(f"{b}: no pack row (dimension unknown)")
        if b in todo:
            if emit(b, n):
                done.append(b)
        elif os.path.exists(f"{OUT}/{camel(b)}.lean"):
            done.append(b)
    aggregator(done)

if __name__ == "__main__":
    main()

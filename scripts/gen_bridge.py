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
# every suite benchmark's Assumption 1 is unconditional (the detumble family carries its momentum
# band in the right evolve domain); no region-conditioned instances remain
BAND = {}

# the choice benchmarks (benchmarks/choice): records under InstancesV2/Choice, the general
# instances' namespaces and Assumption 1 at ε = 1
CHOICE = {
    "vehicle_hypercert": dict(ns="ChoiceVehicleHypercert", G="Gr", n=2),
    "vehicle_accel_copy": dict(ns="ChoiceVehicleAccelCopy", G="Gr", n=2),
    "watertank_choice": dict(ns="ChoiceWatertank", G="GrP", n=2),
}

KEYED = {"acc_spoof_limp", "acc_tune_limp", "platoon3_linkloss", "platoon_delay_linkloss",
         "rover3tier_rung12", "rover_patrol_refine", "rover_patrol_zones",
         "sat3w_detumble_phases", "sat_detumble_phases", "story1_attdist_rung_a_6to8",
         "story1_attdist_rung_b_12dof", "story3_rollover_ladder_rung_b"}


def all_benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt")) + \
        sorted(CHOICE)

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
                m = re.search(rf"theorem {b}_wellFormedR_onBand\s*:\s*WellFormedRIn (\w+) (\w+) \w+ \(epsR", src)
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
{record_imports}
namespace RelCertifier.Bridge.{camel}

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.{ir}
abbrev cX := Oracle.{cuts}
abbrev cov := {b}_coverV2
abbrev prog := Progress.{b}_coverV2_progress
abbrev ce := {cerec}

theorem struct_ok : structOK IR {n} cov cX = true := by decide +kernel
theorem prog_ok : progOK IR {n} cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR {n} cov ce = true := by decide +kernel
{rows_thm}theorem nR_eq : nR IR = {ns}.{G}.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR {ns}.{G} = true := by decide +kernel
theorem src_ok : edgesSrcOK IR {ns}.{G} = true := by decide +kernel
{eps_thm}
/-- The same modes in the generic automaton. -/
theorem modes_eq : ∀ q m', (grOf IR {n} (prunedOf cov)).modeAt q = some m' →
    ∃ m, {ns}.{G}.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, {ns}.{modeAt} q hq, rfl, rfl⟩

{region_block}

{claim}
end RelCertifier.Bridge.{camel}
'''

WINDOW_CLAIM = '''/-- **Theorem 3 of `{b}`** (window form): every verdict group of the benchmark `unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR {n} cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt
'''

KEYED_CLAIM = '''/-- **Theorem 3 of `{b}`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR {n} cX cov reg 0 1 2 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2
    (by decide) (by decide) (by decide) dt hdt
'''

SUITE_REGION = """/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var {n}) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR {n} (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `{ns}.{wfname}`. -/
theorem wellFormedR : WellFormedRIn (grOf IR {n} (prunedOf cov)) (guardR IR {n}) reg (epsR IR) :=
  wellFormedR_transport ({wfterm}) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
    (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))"""

BAND_REGION = """/-- Assumption 1 holds on the momentum band `{ns}.{regname}` (the unconditional form is false:
`{ns}.{b}_wellFormedR_false`); the band is kept by every right flow. -/
noncomputable abbrev reg : Formula (Var {n}) := {ns}.{regname}
theorem reg_fv : reg.fv ⊆ range Rv := by
  intro x hx
  simp only [reg, {ns}.{regname}, {unfold}, Formula.fv, Term.fv, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false, false_or] at hx
  repeat' rcases hx with hx | hx
  all_goals first | (subst hx; exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩ | simp_all
theorem reg_inv : RegionInvariant (grOf IR {n} (prunedOf cov)) reg :=
  regionInvariant_transport {ns}.{b}_band_invariant modes_eq

/-- Assumption 1 on the band, transported from `{ns}.{b}_wellFormedR_onBand`. -/
theorem wellFormedR : WellFormedRIn (grOf IR {n} (prunedOf cov)) (guardR IR {n}) reg (epsR IR) :=
  wellFormedRIn_transport {ns}.{b}_wellFormedR_onBand (by rw [grOf_len, nR_eq]) modes_eq
    (fun q => rfl) (edges_transport_check edges_ok (edgesSrcOK_sound src_ok))"""

# not bridged: its reposition node's progress stages cross their thresholds downward
# (`up = false`); the progress lemmas read upward stages only (hand instance in Choice/General)
SKIP = {"vehicle_hypercert"}

def emit(b, n):
    if b in SKIP:
        print(f"  skipped {b}: downward progress stages (hand-written general instance)")
        return False
    if b in CHOICE:
        c = CHOICE[b]
        info = dict(module=f"RelCertifier.InstancesV2.Choice.General.{camel(b)}", ns=c["ns"],
                    G=c["G"], guard="guardR")
        n = c["n"]
        rec = dict(record_imports=f"import RelCertifier.InstancesV2.Choice.BenchCovers.{b}\n"
                   f"import RelCertifier.InstancesV2.Choice.BenchProgress.{b}\n"
                   f"import RelCertifier.InstancesV2.Choice.BenchChoice.{b}\n",
                   ir=f"{b}_IRc", cuts=f"{b}_cutsCX", cerec=f"Choice.{b}_coverV2_choice",
                   eps_thm="theorem epsR_eq : epsR IR = 1 := by\n"
                   "  have h : Run.parseRat IR.R.epsilon = some (1 : ℚ) := by decide +kernel\n"
                   "  simp only [epsR, h, Option.getD_some, Rat.cast_one]\n",
                   wfname="wellFormedR", wfterm=f"by rw [epsR_eq]; exact {c['ns']}.wellFormedR")
    else:
        info = wf_info(b)
        rec = dict(record_imports=f"import RelCertifier.InstancesV2.BenchCovers.{b}\n"
                   f"import RelCertifier.InstancesV2.BenchProgress.{b}\n",
                   ir=f"{b}_IRv2", cuts=f"{b}_cutsV2X",
                   cerec=f'Choice.ChoiceEmitE.empty "{b}"', eps_thm="",
                   wfname=f"{b}_wellFormedR", wfterm=f"{info['ns'] if info else ''}.{b}_wellFormedR")
    if info is None and b in BAND:
        info = None
    if info is None:
        # Assumption 1 holds only on a region for this benchmark (`WellFormedRIn`); the
        # unconditional form the general theorem takes is not available: not bridged
        print(f"  skipped {b}: no unconditional WellFormedR lemma")
        return False
    keyed = b in KEYED
    modeAt = f"{info['G']}_modeAt"
    rows_thm = "" if keyed else "theorem rows_same : rowsSame IR = true := by decide +kernel\n"
    claim = (KEYED_CLAIM if keyed else WINDOW_CLAIM).format(b=b, n=n)
    if b in BAND:
        region_block = BAND_REGION.format(b=b, n=n, ns=info["ns"], regname=BAND[b]["reg"],
                                          unfold=", ".join(f"{info['ns']}.{u}" for u in BAND[b]["unfold"].split(", ")))
    else:
        region_block = SUITE_REGION.format(n=n, ns=info["ns"], wfname=rec["wfname"], wfterm=rec["wfterm"])
    txt = TEMPLATE.format(b=b, camel=camel(b), n=n, form_mod="Keyed" if keyed else "Window",
                          wfmod=info["module"], ns=info["ns"], G=info["G"], modeAt=modeAt,
                          rows_doc="" if keyed else ", `rows_same`", rows_thm=rows_thm,
                          claim=claim, region_block=region_block, **rec)
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
        n = d.get(b, CHOICE.get(b, {}).get("n"))
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

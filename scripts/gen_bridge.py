#!/usr/bin/env python3
"""Emit the generic-bridge instances: RelCertifier/InstancesV2/Bridge/<Camel>.lean, one per
suite_v2 benchmark, and the aggregator RelCertifier/InstancesV2/Bridge.lean.

Each instance states Theorem 3 of its benchmark through the generic bridge
(`Proofs/Encoding/Emitted/`): the structural bundles decided in the kernel, Assumption 1
transported from the suite's `WellFormedR` lemma and lifted by one coordinate (the right
clock of the clocked right automaton, `Emitted.wellFormedR_lift`), the verdicts assumed as
`Verdicts` (the groups `relcert-bridge-verdicts` discharges). Benchmarks whose left modes
declare one row take the window form (`windowClaim`, three auxiliary coordinates); those with
per-mode rows take the mode-keyed form (`keyedClaim`, four).

The instance's dimension is the Assumption 1 lemma's dimension plus one (`bridgeDimV2`); the
runner sends every query at that dimension, so the instance's `Verdicts` hypothesis is
exactly the runner's queries.

Usage: python3 scripts/gen_bridge.py [bench ...]   (default: all of benchmarks/suite_v2)
"""
import os, re, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
os.chdir(ROOT)
SUITE = "benchmarks/suite_v2"
OUT = "RelCertifier/InstancesV2/Bridge"
WF_DIRS = [("RelCertifier/InstancesV2/WellFormed", "RelCertifier.InstancesV2.WellFormed")]

# benchmarks whose left modes declare distinct rows (the keyed form); every other benchmark's
# rows are identical (`rowsSame`, checked in the kernel by the window instance)
# the choice benchmarks (benchmarks/choice): records under InstancesV2/Choice, the general
# instances' namespaces and Assumption 1 at ε = 1
CHOICE = {
    "vehicle_accel_copy": dict(ns="ChoiceVehicleAccelCopy", G="Gr", n=2),
    "watertank_choice": dict(ns="ChoiceWatertank", G="GrP", n=2),
}

KEYED = {"acc_tune_limp", "antenna_track_kvretune", "elevator_start_discbrake",
         "engine_start_highidle", "h2_refuel_ambientbias", "hydro_rejection_gatecal",
         "platoon_linkloss", "platoon_profiles", "syringe_relay_prearm", "molding_pack_checkring",
         "ventilator_vc_cuffleak", "lit_csf25_salt_tank_hold",
         "turbine_startup_gearratio", "boiler_purge_vfd", "autoclave_liquid_steambank"}


def all_benches():
    return sorted(d for d in os.listdir(SUITE) if os.path.isfile(f"{SUITE}/{d}/input.txt")) + \
        sorted(CHOICE)

def camel(b):
    return "".join(w.capitalize() for w in b.split("_"))

def dims():
    """The Assumption 1 dimension of each benchmark: the pack table's `dim` (the instance is
    emitted one higher, `bridgeDimV2`)."""
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
                md = re.search(rf"theorem {b}_wellFormedR_direct\b", src)
                if md:
                    ns = re.findall(r"^namespace (\w+)", src, re.M)
                    ns = [x for x in ns if x != "RelCertifier"]
                    return dict(module=f"{modbase}.{fn[:-5]}", ns=ns[-1], G=None, guard=None, direct=True)
                continue
            ns = re.findall(r"^namespace (\w+)", src, re.M)
            ns = [x for x in ns if x != "RelCertifier"]
            return dict(module=f"{modbase}.{fn[:-5]}", ns=ns[-1], G=m.group(1), guard=m.group(2))
    # a hand-written general instance with Assumption 1 at the literal period 1
    # (`theorem wellFormedR : WellFormedR G guardR 1`; the instance proves `epsR IR = 1`)
    fn = f"RelCertifier/InstancesV2/Choice/General/{camel(b)}.lean"
    if os.path.exists(fn):
        src = open(fn).read()
        m = re.search(r"theorem wellFormedR\s*:\s*WellFormedR (\w+) (\w+) 1\b", src)
        if m:
            ns = re.findall(r"^namespace (\w+)", src, re.M)
            ns = [x for x in ns if x != "RelCertifier"]
            mn = re.search(r"Formula \(Var (\d+)\)", src)
            return dict(module=f"RelCertifier.InstancesV2.Choice.General.{camel(b)}", ns=ns[-1],
                        G=m.group(1), guard=m.group(2), eps1=True, n=int(mn.group(1)) if mn else None)
    return None

TEMPLATE = '''/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`{rows_doc}, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension {n0} and lifted to {n} (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.{form_mod}
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
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
theorem pad_ok : padOK IR {n0} = true := by decide +kernel
{rows_thm}{transport_block}{region_block}

{claim}
end RelCertifier.Bridge.{camel}
'''

WINDOW_CLAIM = '''/-- **Theorem 3 of `{b}`** (window form): every verdict group of the benchmark `unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR {n} cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt
'''

KEYED_CLAIM = '''/-- **Theorem 3 of `{b}`** (mode-keyed form): every verdict group of the benchmark
`unsat`. -/
theorem {b}_bridge (hv : Verdicts IR {n} cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    keyedClaim IR {n} cX cov reg 0 1 2 3 dt :=
  theorem3_keyed_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) dt hdt
'''

TRANSPORT_BLOCK = """theorem nR_eq : nR IR = {ns}.{G}.modes.length := by decide +kernel
theorem edges_ok : edgesCovered IR {ns}.{G} = true := by decide +kernel
theorem src_ok : edgesSrcOK IR {ns}.{G} = true := by decide +kernel
{eps_thm}
/-- The same modes in the generic automaton (at the lemma's dimension). -/
theorem modes_eq : ∀ q m', (grOf IR {n0} (prunedOf cov)).modeAt q = some m' →
    ∃ m, {ns}.{G}.modeAt q = some m ∧ m.sys = m'.sys ∧ m.dom = m'.dom := fun q m' hm' => by
  obtain ⟨hq, rfl⟩ := grOf_modeAt_inv hm'
  rw [nR_eq] at hq
  exact ⟨_, {ns}.{modeAt} q hq, rfl, rfl⟩

"""

DIRECT_REGION = """/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var {n}) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR {n} (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension {n0}
(`{ns}.{b}_wellFormedR_direct`), lifted to {n}. -/
theorem wellFormedR : WellFormedRIn (grOf IR {n} (prunedOf cov)) (guardR IR {n}) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := {n0}) pad_ok
    ({ns}.{b}_wellFormedR_direct (prunedOf cov))) reg"""

SUITE_REGION = """/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var {n}) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR {n} (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, transported from `{ns}.{wfname}` at dimension {n0} and lifted to {n}. -/
theorem wellFormedR : WellFormedRIn (grOf IR {n} (prunedOf cov)) (guardR IR {n}) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := {n0}) pad_ok
    (wellFormedR_transport ({wfterm}) (by rw [grOf_len, nR_eq]) modes_eq (fun q => rfl)
      (edges_transport_check edges_ok (edgesSrcOK_sound src_ok)))) reg"""

# benchmarks without a generated instance (none; a downward single progress stage is covered
# by `repoProgress_one_down`, a two-stage certificate must be upward in both stages)
SKIP = set()

STUTTER_THMS = """/-- The benchmark opts in to stretch 0 (`stutter = true`), and its cover really uses a
stretch-0 pairing (decided in the kernel). -/
theorem stutter_on : IR.stutter = true := by decide +kernel
theorem uses_stutter : (cov.covers.any fun lc => lc.strata.any (·.lamN == 0)) = true := by
  decide +kernel
"""

def emit(b, n0):
    """Emit `b`'s instance at dimension `n0 + 1`, `n0` the dimension of its Assumption 1 lemma."""
    n = n0 + 1
    if b in SKIP:
        print(f"  skipped {b}: downward progress stages (hand-written general instance)")
        return False
    if b in CHOICE:
        c = CHOICE[b]
        info = dict(module=f"RelCertifier.InstancesV2.Choice.General.{camel(b)}", ns=c["ns"],
                    G=c["G"], guard="guardR")
        n0 = c["n"]
        n = n0 + 1
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
        rec = dict(record_imports=f"import RelCertifier.InstancesV2.Cuts.{b}\n"
                   f"import RelCertifier.InstancesV2.BenchCovers.{b}\n"
                   f"import RelCertifier.InstancesV2.BenchProgress.{b}\n"
                   f"import RelCertifier.InstancesV2.BenchChoice.{b}\n",
                   ir=f"{b}_IRv2", cuts=f"{b}_cutsV2X",
                   cerec=f"Choice.{b}_coverV2_choice", eps_thm="",
                   wfname=f"{b}_wellFormedR", wfterm=f"{info['ns'] if info else ''}.{b}_wellFormedR")
        if info and info.get("eps1"):
            rec.update(eps_thm="theorem epsR_eq : epsR IR = 1 := by\n"
                       "  have h : Run.parseRat IR.R.epsilon = some (1 : ℚ) := by decide +kernel\n"
                       "  simp only [epsR, h, Option.getD_some, Rat.cast_one]\n",
                       wfname="wellFormedR", wfterm=f"by rw [epsR_eq]; exact {info['ns']}.wellFormedR")
    if info is None:
        print(f"  skipped {b}: no WellFormedR lemma")
        return False
    keyed = b in KEYED
    direct = info.get("direct", False)
    modeAt = None if direct else f"{info['G']}_modeAt"
    rows_thm = "" if keyed else "theorem rows_same : rowsSame IR = true := by decide +kernel\n"
    src = f"{SUITE}/{b}/input.txt"
    if os.path.exists(src) and re.search(r"(?m)^\s*stutter\s*=\s*true\s*$", open(src).read()):
        # the opt-in stretch 0 (`docs/STUTTER.md`): the IR carries the key and the cover uses a
        # stretch-0 pairing, both decided in the kernel (`structOK`'s `timeOK` admits `lamN = 0`
        # only under the key)
        rows_thm += STUTTER_THMS
    claim = (KEYED_CLAIM if keyed else WINDOW_CLAIM).format(b=b, n=n)
    if direct:
        region_block = DIRECT_REGION.format(n=n, n0=n0, ns=info["ns"], b=b)
        transport_block = ""
    else:
        region_block = SUITE_REGION.format(n=n, n0=n0, ns=info["ns"], wfname=rec["wfname"], wfterm=rec["wfterm"])
        transport_block = TRANSPORT_BLOCK.format(n0=n0, ns=info["ns"], G=info["G"], modeAt=modeAt, eps_thm=rec["eps_thm"])
    txt = TEMPLATE.format(b=b, camel=camel(b), n=n, n0=n0, form_mod="Keyed" if keyed else "Window",
                          wfmod=info["module"], ns=info["ns"], G=info["G"], modeAt=modeAt,
                          rows_doc="" if keyed else ", `rows_same`", rows_thm=rows_thm,
                          claim=claim, region_block=region_block, transport_block=transport_block,
                          **{k: v for k, v in rec.items() if k != "eps_thm"})
    os.makedirs(OUT, exist_ok=True)
    with open(f"{OUT}/{camel(b)}.lean", "w") as f:
        f.write(txt)
    return True

def aggregator(benches):
    with open("RelCertifier/InstancesV2/Bridge.lean", "w") as f:
        f.write("/- The generic-bridge instances of suite_v2 (GENERATED by `scripts/gen_bridge.py`). -/\n")
        for b in benches:
            f.write(f"import RelCertifier.InstancesV2.Bridge.{camel(b)}\n")

def nvars(b):
    """The left state variables of `b` (its input file's `state_vars`)."""
    for line in open(f"{SUITE}/{b}/input.txt"):
        if line.startswith("state_vars"):
            return len([v for v in line.split("[", 1)[1].split("]")[0].split(",") if v.strip()])
    return 1

def main():
    benches = all_benches()
    todo = sys.argv[1:] or benches
    d = dims()
    done = []
    for b in benches:
        n = d.get(b, CHOICE.get(b, {}).get("n"))
        if n is None:
            # no standalone pack row: the bridge runner's fallback (`bridgeDimV2`, before its
            # `+ 1`): a hand-written general instance's dimension, else the state variables
            # padded to three coordinates (right mode variable, left clock, stored left
            # mode); the right clock, the keyed form's fourth, is the `+ 1`
            info0 = wf_info(b)
            n = info0.get("n") if info0 and info0.get("eps1") and info0.get("n") else max(nvars(b), 3)
        if b in todo:
            if emit(b, n):
                done.append(b)
        elif os.path.exists(f"{OUT}/{camel(b)}.lean"):
            done.append(b)
    aggregator(done)

if __name__ == "__main__":
    main()

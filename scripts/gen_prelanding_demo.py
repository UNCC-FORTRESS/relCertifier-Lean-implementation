#!/usr/bin/env python3
"""Emit the pre-landing demos (benchmarks/prelanding_demo: engine_cooling_prelanding, non-strict
rows; hold_reposition_strict, a strict row; docs/PRELANDING.md) through the existing generator
path, without touching the suite_v2 aggregators.

* the data leaves (IR, cover, progress, choice, cuts) by `gen_v2_data.emit_leaves`, reading
  benchmarks/prelanding_demo instead of benchmarks/suite_v2 (the leaves land beside the suite's,
  named after the demo; no aggregator is rewritten, so the suite tables are unchanged); the IR
  carries `prelanding := true`; the same `--emit-cover` run writes the pre-landing record
  (`RELCERT_PRELANDING_OUT`) to InstancesV2/BenchPrelanding/<b>.lean;
* the generic-bridge instance InstancesV2/Bridge/<Camel>.lean, in the window form (one row), at
  dimension 3 (+1, the right clock), over the cover merged with the pre-landing record
  (`withPL`), with Theorem 3 over the EMITTED cover (`theorem3_window_of_records_pl`, the strict
  chain's `theorem3_window_strict_of_records_pl` at a strict row) from the records and from a
  green run of the groups (`bridgeGroups`, `bridgeGroupsS`; the reposition groups are on each
  node's region, `dynRegionI`). Assumption 1 is each demo's own Z3-free lemma
  (InstancesV2/WellFormed/<Camel>.lean), lifted by one coordinate.

Usage: python3 scripts/gen_prelanding_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding
              lake build RelCertifier.InstancesV2.Bridge.HoldRepositionStrict
Verdicts:     lake env lean scripts/prelanding_demo_verdicts.lean
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D

DEMO_DIR = "benchmarks/prelanding_demo"
DEMOS = [("engine_cooling_prelanding", "EngineCoolingPrelanding", False),
         ("hold_reposition_strict", "HoldRepositionStrict", True)]
PL_LEAF = None

D.SUITE = DEMO_DIR
D.HDR = D.HDR.replace("(suite_v2)", "(prelanding_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_prelanding_demo.py`.")

_run = D.run


def run(args, env_extra=None):
    """`gen_v2_data.run`, with the pre-landing record written by the same `--emit-cover` run."""
    if "--emit-cover" in args:
        env_extra = dict(env_extra or {}, RELCERT_PRELANDING_OUT=PL_LEAF)
    return _run(args, env_extra)


D.run = run

INSTANCE = '''/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `{b}` (prelanding_demo) through the generic bridge (GENERATED —
`scripts/gen_prelanding_demo.py`)

With the opt-in key `prelanding = true` (`docs/PRELANDING.md`) the cover's right-only nodes are
pre-landing nodes, recorded in the pre-landing record `pl`, never as the cover's
`dynPre`/`dynPost` flags. The kernel merges them (`withPL`) for the cover graph; each node's
reposition pack is on its region (`dynRegion`: before its progress certificate's last threshold,
strict components on the closure).

Theorem 3 of the benchmark from its emitted records{strict_doc}: the structural bundles decided in the
kernel on the merged cover (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), the data
gate `pl_ok` (the key is set, the whole-domain flags are off), Assumption 1 from the demo's own
lemma at dimension 3 lifted to 4 (the right clock), the verdicts assumed (`{verd}`: the groups
`scripts/prelanding_demo_verdicts.lean` discharges, `Emitted.{verd_of}`). The claim is over the
emitted cover `cov`.
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.{chain_mod}
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.{camel}
import RelCertifier.InstancesV2.Cuts.{b}
import RelCertifier.InstancesV2.BenchCovers.{b}
import RelCertifier.InstancesV2.BenchProgress.{b}
import RelCertifier.InstancesV2.BenchChoice.{b}
import RelCertifier.InstancesV2.BenchPrelanding.{b}

namespace RelCertifier.Bridge.{camel}

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.{b}_IRv2
abbrev cX := Oracle.{b}_cutsV2X
abbrev cov := {b}_coverV2
abbrev prog := Progress.{b}_coverV2_progress
abbrev ce := Choice.{b}_coverV2_choice
abbrev pl := Preland.{b}_coverV2_prelanding
/-- The cover graph's rows: the emitted cover with the pre-landing nodes merged in. -/
abbrev covM := withPL cov pl

/-- The data gate: the key is set and the emitted whole-domain flags are all off. -/
theorem pl_ok : plOK IR cov pl = true := by decide +kernel
theorem struct_ok : structOK IR 4 covM cX = true := by decide +kernel
theorem prog_ok : progOK IR 4 covM prog = true := by decide +kernel
theorem covers_ok : coversOK IR 4 covM ce = true := by decide +kernel
theorem pad_ok : padOK IR 3 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 4) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 4 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 3
(`V2{camel}.{b}_wellFormedR_direct`), lifted to 4. -/
theorem wellFormedR : WellFormedRIn (grOf IR 4 (prunedOf cov)) (guardR IR 4) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 3) pad_ok
    (V2{camel}.{b}_wellFormedR_direct (prunedOf cov))) reg

/-- The demo opts in, and its cover really uses pre-landing nodes (decided in the kernel). -/
theorem prelanding_on : IR.prelanding = true := by decide +kernel
theorem uses_prelanding : pl.nodes.isEmpty = false := by decide +kernel
{strict_facts}
/-- **Theorem 3 of `{b}`** (window form, over the emitted cover): every verdict group of the
benchmark `unsat`. -/
theorem {b}_bridge (hv : {verd} IR 4 cX covM prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    {claim} IR 4 cX cov reg 0 1 2 dt :=
  {thm} pl_ok struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

/-- The same from a green run of the benchmark's groups (`{groups}`,
`scripts/prelanding_demo_verdicts.lean`). -/
theorem {b}_bridge_run {{gs : List (List (IForm 4))}}
    (hrun : {groups} IR 4 cX covM prog ce = some gs) (hok : GroupsOK gs) (dt : ℝ)
    (hdt : dt ≤ epsL IR) : {claim} IR 4 cX cov reg 0 1 2 dt :=
  {b}_bridge ({verd_of} hrun hok) dt hdt

end RelCertifier.Bridge.{camel}
'''

STRICT_FACTS = '''
/-- The row really carries a strict atom (`y_L < y_R + 5` strict, `y_R ≤ 0` closure), decided in
the kernel; the strict chain applies. -/
theorem masks : (List.range (nL IR)).map (maskOf IR 4) = [[true, false]] := by decide +kernel
theorem not_collapse : noStrictRows IR 4 = false := by decide +kernel
'''


def main():
    global PL_LEAF
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    for B, CAMEL, strict in DEMOS:
        PL_LEAF = f"{D.OUT}/BenchPrelanding/{B}.lean"
        D.emit_leaves(B)
        fn = f"{D.OUT}/BenchIR/{B}.lean"
        txt = open(fn).read().replace(f"benchmarks/suite_v2/{B}/", f"{DEMO_DIR}/{B}/")
        open(fn, "w").write(txt)
        pl = open(PL_LEAF).read()
        if "PrelandEmitE" not in pl:
            sys.exit(f"{B}: no pre-landing record written")
        open(PL_LEAF, "w").write(D.HDR.format(b=B, what="emitted pre-landing record") + pl)
        print(f"  emitted leaves of {B}")
        out = f"RelCertifier/InstancesV2/Bridge/{CAMEL}.lean"
        if strict:
            kw = dict(chain_mod="StrictRun", verd="VerdictsS", verd_of="verdictsS_of_groups",
                      groups="bridgeGroupsS", claim="windowClaimS",
                      thm="theorem3_window_strict_of_records_pl", strict_facts=STRICT_FACTS,
                      strict_doc=" at its strict row (the strict chain)")
        else:
            kw = dict(chain_mod="Run", verd="Verdicts", verd_of="verdicts_of_groups",
                      groups="bridgeGroups", claim="windowClaim",
                      thm="theorem3_window_of_records_pl", strict_facts="", strict_doc="")
        open(out, "w").write(INSTANCE.format(b=B, camel=CAMEL, **kw))
        print(f"  emitted {out} (dim 4)")


if __name__ == "__main__":
    main()

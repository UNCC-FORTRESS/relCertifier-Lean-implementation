#!/usr/bin/env python3
"""Emit the stutter demo (benchmarks/stutter_demo/salt_tank_stutter, docs/STUTTER.md) through the
existing generator path, without touching the suite_v2 aggregators.

* the data leaves (IR, cover, progress, choice, pre-landing record, cuts) by
  `gen_v2_data.emit_leaves`, reading benchmarks/stutter_demo instead of benchmarks/suite_v2 (the
  leaves land beside the suite's, named after the demo; no aggregator is rewritten, so the suite
  tables are unchanged); the IR records the run's features (stretch 0 and the pre-landing
  certificate, both always on since 2026-10-31) and the cover has a stretch-0 pairing (`lamN = 0`);
* the generic-bridge instance by `gen_bridge.emit` (the pre-landing instance, the cover having
  pre-landing right-only nodes), in the window form (the rows are the same in every left mode), at
  the suite salt tank's dimension 3 (+1, the right clock), with Theorem 3 from the records
  (`Verdicts`) and from a green run of the groups (`bridgeGroups` on the merged cover);
  `stutter_on` / `uses_stutter` decided in the kernel. Assumption 1 is transported from the suite's
  `lit_nahs25_salt_tank` lemma: the demo's right model is the suite file's, checked in the kernel
  by the transport's `nR_eq`, `edges_ok`, `src_ok`.

Usage: python3 scripts/gen_stutter_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter
Verdicts:     lake env lean scripts/stutter_demo_verdicts.lean
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D
import gen_bridge as G

DEMO_DIR = "benchmarks/stutter_demo"
B = "salt_tank_stutter"
WF_FROM = "lit_nahs25_salt_tank"   # the suite benchmark with the same right model

D.SUITE = DEMO_DIR
G.SUITE = DEMO_DIR
D.HDR = D.HDR.replace("(suite_v2)", "(stutter_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_stutter_demo.py`.")

_wf_info = G.wf_info
G.wf_info = lambda b: _wf_info(WF_FROM if b == B else b)

TITLE = "# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)"
DEMO_TITLE = ("# `{b}` (stutter_demo) through the generic bridge (GENERATED —\n"
              "`scripts/gen_stutter_demo.py`)\n\nThe attacked Off's pairings are stretch-0 "
              "segments: the\nrecord's `lamN = 0`, admitted by `timeOK` because the IR records that "
              "stretch 0 is allowed\n(`stutter = true`, the default) and the file declares `lambda_min = 0` "
              "(`Run.stutterAllowed`).")
for t in ("TEMPLATE", "PL_TEMPLATE"):
    assert TITLE in getattr(G, t), t
    setattr(G, t, getattr(G, t).replace(TITLE, DEMO_TITLE))


def main():
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    D.emit_leaves(B)
    fn = f"{D.OUT}/BenchIR/{B}.lean"
    txt = open(fn).read().replace(f"benchmarks/suite_v2/{B}/", f"{DEMO_DIR}/{B}/")
    open(fn, "w").write(txt)
    print(f"  emitted leaves of {B}")
    n = 3          # the suite salt tank's Assumption 1 dimension; the instance is emitted at n + 1
    if not G.emit(B, n):
        sys.exit(f"{B}: bridge instance not emitted")
    fn = f"{G.OUT}/{G.camel(B)}.lean"
    txt = open(fn).read().replace(f"{B}_wellFormedR", f"{WF_FROM}_wellFormedR")
    assert txt.count("theorem stutter_on") == 1, "the instance does not state stutter_on once"
    open(fn, "w").write(txt)
    print(f"  emitted RelCertifier/InstancesV2/Bridge/{G.camel(B)}.lean (dim {n + 1})")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Emit the mixed-shape progress demo (benchmarks/progress_demo/stopline_friction_mixed,
docs/PRELANDING.md "Two-stage certificates in every direction") through the existing generator
path, without touching the suite_v2 aggregators.

* the data leaves (IR, cover, progress, choice, pre-landing record, cuts) by
  `gen_v2_data.emit_leaves`, reading benchmarks/progress_demo instead of benchmarks/suite_v2 (the
  leaves land beside the suite's, named after the demo; no aggregator is rewritten, so the suite
  tables are unchanged). The pre-landing record has right-BRAKE nodes whose progress certificate
  is two stages, a helper UP (`b >= 2`) and a DOWNWARD landing (`v <= 7/20`): the shape
  `Progress.repoProgress_two_ud_reg` covers (checked here: the emitted record must have one);
* the generic-bridge instance by `gen_bridge.emit` (the pre-landing instance over the cover
  merged with the record, `withPL`; the mode-keyed form, the rows differing by left mode), at
  dimension 3 (+1, the right clock), with Theorem 3 from the records (`Verdicts`) and from a green
  run of the groups (`bridgeGroups` on the merged cover). `prog_ok : progOK IR 4 covM prog` is
  decided in the kernel on the merged cover, the mixed-shape nodes included. Assumption 1 is the
  demo's own Z3-free lemma (InstancesV2/WellFormed/StoplineFrictionMixed.lean).

Usage: python3 scripts/gen_progress_demo.py
Kernel check: lake build RelCertifier.InstancesV2.Bridge.StoplineFrictionMixed
Verdicts:     lake env lean scripts/progress_demo_verdicts.lean
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_v2_data as D
import gen_bridge as G

DEMO_DIR = "benchmarks/progress_demo"
B = "stopline_friction_mixed"

D.SUITE = DEMO_DIR
G.SUITE = DEMO_DIR
G.KEYED = set(G.KEYED) | {B}
D.HDR = D.HDR.replace("(suite_v2)", "(progress_demo)").replace(
    "Regenerate with `scripts/gen_v2_data.py {b}`.", "Regenerate with `scripts/gen_progress_demo.py`.")

TITLE = "# `{b}` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py {b}`)"
DEMO_TITLE = ("# `{b}` (progress_demo) through the generic bridge (GENERATED —\n"
              "`scripts/gen_progress_demo.py`)\n\nThe pre-landing nodes with the right in BRAKE "
              "carry a reposition certificate whose two stages\ncross in opposite directions (a helper up, "
              "then a downward landing), accepted by `certOK`\n(`Progress.lean`'s "
              "`repoProgress_two_ud_reg`).")
for t in ("TEMPLATE", "PL_TEMPLATE"):
    assert TITLE in getattr(G, t), t
    setattr(G, t, getattr(G, t).replace(TITLE, DEMO_TITLE))


def mixed_certs(path):
    """The emitted certificates of `path` with two stages, a helper up and a landing down."""
    txt = open(path).read()
    st = r'⟨"(\w+)", \(-?\d+ : ℚ\) / \d+, (true|false), \(\d+ : ℚ\) / \d+⟩'
    pat = re.compile(r'⟨"(\w+)", "(\w+)", (true|false), \[' + st + ", " + st + r'\]')
    return [m.groups() for m in pat.finditer(txt) if m.group(5) == "true" and m.group(7) == "false"]


def main():
    for d in ["BenchIR", "BenchCovers", "Cuts", "BenchProgress", "BenchChoice", "BenchPrelanding"]:
        os.makedirs(f"{D.OUT}/{d}", exist_ok=True)
    D.emit_leaves(B)
    fn = f"{D.OUT}/BenchIR/{B}.lean"
    txt = open(fn).read().replace(f"benchmarks/suite_v2/{B}/", f"{DEMO_DIR}/{B}/")
    open(fn, "w").write(txt)
    print(f"  emitted leaves of {B}")
    mixed = mixed_certs(f"{D.OUT}/BenchProgress/{B}.lean")
    if not mixed:
        sys.exit(f"{B}: no helper-up / landing-down certificate emitted (the demo's point)")
    print(f"  {len(mixed)} mixed (up, down) certificates: " +
          ", ".join(f"{m[0]}/{m[1]} pre={m[2]}" for m in mixed))
    n = 3          # the demo's Assumption 1 dimension; the instance is emitted at n + 1
    if not G.emit(B, n):
        sys.exit(f"{B}: bridge instance not emitted")
    print(f"  emitted RelCertifier/InstancesV2/Bridge/{G.camel(B)}.lean (dim {n + 1})")


if __name__ == "__main__":
    main()

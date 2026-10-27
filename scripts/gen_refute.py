#!/usr/bin/env python3
"""Emit the kernel refutation instances (branch `refutation`; the `gen_bridge.py` pattern).

From the finder's witnesses (`docs/refute/witnesses.jsonl`, `scripts/refute_finder.py`), per
mutant with a witness:

* `benchmarks/refute_mutants/<id>/input.txt`: the mutated benchmark file;
* `RelCertifier/InstancesV2/Refute/Data/<id>.lean`: its parser-emitted IR (`relcert --emit-ir`)
  and the witness literal;
* `RelCertifier/InstancesV2/Refute/<Camel>.lean`: the refutation, `¬ keyedClaim …` (the clocked
  claim, the one the bridge instances prove) for every cover record, from the kernel-decided
  witness facts and the verdicts `RefVerdicts` (the groups `relcert-refute-verdicts` discharges);

The instance's dimension is the bridge dimension of its benchmark (`bridgeDimV2`: the witness's
`dim`, the Assumption 1 lemma's dimension, plus one for the right clock), so each `¬ keyedClaim
IR n cX cov Formula.tt 0 1 2 3 dt` is literally the negation of the benchmark's bridge claim at
the same dimension (`0 1 2 3`: right mode variable, left clock, left mode variable, right
clock; the window form has no left mode variable, `0 1 2`).

and the aggregators `RelCertifier/InstancesV2/Refute/Table.lean` (the runner's records and its
declared group count) and `RelCertifier/InstancesV2/Refute.lean` (every instance).

The cut certificate is the suite benchmark's (`Oracle.<bench>_cutsV2X`): the tool computes the
kept cut atoms from the model alone (`checkedCutX` per mode, no invariant input), and every
instance proves the mutant has the benchmark's model (`same_model`).

Where a mutant's text comes from (2026-10-27; before, every record's text was copied from the
finder's scratch path `rec["file"]`, which for benchmarks the last run did not visit held another
run's file, and about 50 committed mutant inputs were silently rewritten). A record written by
the finder now carries the SHA-256 of the mutant text it searched (`sha256`) and a per-run
scratch path. The text used is, in this order: that run's scratch file if its hash matches; the
committed `benchmarks/refute_mutants/<id>/input.txt` if the record has no hash (a record from
before the change) or the hash matches. Anything else is an error. Every text must also be
mutant `idx` of the CURRENT suite file (same operator and label, the same non-comment lines as
the finder's enumeration regenerates), else an error ("rerun the finder for that benchmark").
All errors are reported together and nothing is written. Each mutant input written is listed,
and files under `benchmarks/refute_mutants` and `InstancesV2/Refute` that no record produces
(orphans of removed benchmarks) are listed too.

Usage: python3 scripts/gen_refute.py [--witnesses FILE]
"""
import argparse, hashlib, json, os, re, subprocess, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import refute_finder as F  # noqa: E402  (the finder's mutant enumeration)
os.chdir(ROOT)
RELCERT = os.path.join(ROOT, ".lake/build/bin/relcert")
OUT = "RelCertifier/InstancesV2/Refute"
MUT = "benchmarks/refute_mutants"

HDR = """/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# {title} (GENERATED — `scripts/gen_refute.py`)
{body}-/
"""


def camel(s):
    return "".join(w.capitalize() for w in s.split("_"))


def lean_rat(s):
    s = s.strip()
    if "/" in s:
        a, b = s.split("/")
        return f"({a}/{b} : ℚ)" if not a.startswith("-") else f"(-{a[1:]}/{b} : ℚ)"
    return f"({s} : ℚ)"


def nr_groups(rec):
    """The number of query groups of a refutation: one per right mode."""
    return rec["nR"]


def sha256(text):
    return hashlib.sha256(text.encode()).hexdigest()


def body(text):
    """The non-comment, non-blank lines of an input file (the model and the rows)."""
    return [l for l in text.splitlines() if l.strip() and not l.lstrip().startswith("#")]


def mutant_text(rec):
    """The mutant text of a record (see the module docstring); raises ValueError otherwise."""
    b, i = rec["bench"], rec["idx"]
    mid = f"{b}_m{i:03d}"
    dst = f"{MUT}/{mid}/input.txt"
    rerun = f"rerun `scripts/refute_finder.py --only {b}` (it replaces that benchmark's records in --out)"
    h = rec.get("sha256")
    text = None
    if h is not None and os.path.exists(rec["file"]):
        t = open(rec["file"]).read()
        if sha256(t) == h:
            text = t
    if text is None and os.path.exists(dst):
        t = open(dst).read()
        if h is None or sha256(t) == h:
            text = t
    if text is None:
        why = ("its run's scratch file is missing or was overwritten, and no committed copy has "
               "its hash" if h is not None else
               "a record from before the hash field, and no committed copy")
        raise ValueError(f"{mid}: no mutant text from the finder run that found its witness ({why}); {rerun}")
    src = open(f"benchmarks/suite_v2/{b}/input.txt").read()
    bb, rows = F.load_rows(src)
    muts = F.mutants(rows, bb["L"]["vars"], bb["R"]["vars"])
    if i >= len(muts) or (muts[i][0], muts[i][1]) != (rec["op"], rec["mutant"]):
        raise ValueError(f"{mid}: the current suite file has no mutant {i} = {rec['op']} "
                         f"`{rec['mutant']}`; {rerun}")
    op, label, key, new = muts[i]
    if body(text) != body(F.write(src, F.apply(rows, key, new))):
        raise ValueError(f"{mid}: the mutant text differs from mutant {i} of the current suite file "
                         f"(the benchmark changed since the finder ran); {rerun}")
    return text


def emit(rec, text, written):
    b, i = rec["bench"], rec["idx"]
    mid = f"{b}_m{i:03d}"
    w = rec["witness"]
    os.makedirs(f"{MUT}/{mid}", exist_ok=True)
    dst = f"{MUT}/{mid}/input.txt"
    if not os.path.exists(dst) or open(dst).read() != text:
        with open(dst, "w") as f:
            f.write(text)
        written.append(dst)
    ir = subprocess.run([RELCERT, "--emit-ir", f"{MUT}/{mid}/input.txt", f"{mid}_IRm"],
                        capture_output=True, text=True, check=True).stdout
    ir = "\n".join(l for l in ir.splitlines() if not l.startswith("/-- Parser-emitted IR"))
    os.makedirs(f"{OUT}/Data", exist_ok=True)
    with open(f"{OUT}/Data/{mid}.lean", "w") as f:
        f.write(HDR.format(title=f"`{mid}`: a mutant of `{b}` and its refutation witness",
                           body=f"\nMutant {rec['op']} `{rec['mutant']}` of `benchmarks/suite_v2/{b}`; file "
                                f"`{MUT}/{mid}/input.txt`.\n"))
        f.write("import RelCertifier.Trusted.Parse\nimport RelCertifier.Trusted.RefuteQueries\n\n"
                "namespace RelCertifier.Refute\n\nopen RelCertifier.Parse\n\n")
        f.write(f"/-- Parser-emitted IR of `{MUT}/{mid}/input.txt` (do not edit). -/\n")
        f.write(ir.strip() + "\n\n")
        f.write(f"/-- The finder's witness (kind {w['kind']}). -/\n")
        f.write(f"def {mid}_wit : RefWitE :=\n"
                f"  {{ kind := \"{w['kind']}\", u := {w['u']}, m := {w['m']}, q0 := {w['q0']}, k := {w['k']},\n"
                f"    wL := [{', '.join(lean_rat(x) for x in w['wL'])}],\n"
                f"    wR := [{', '.join(lean_rat(x) for x in w['wR'])}] }}\n\n")
        f.write("end RelCertifier.Refute\n")
    n = rec["dim"] + 1  # the bridge dimension: the witness's `dim` plus the right clock
    C = camel(mid)
    kind = w["kind"]
    window = bool(rec.get("rowsSame"))
    desc = {"C": "no partner", "A": "a component broken at the switch, right-rigid",
            "B": "a component pushed out by the left flow, right-rigid"}[kind]
    run = (f"the left takes the window of mode {w['m']}" if window else
           f"the left switches\nfrom mode {w['u']} to mode {w['m']}")
    flow = "a zero-duration flow" if kind != "B" else "a short flow"
    with open(f"{OUT}/{C}.lean", "w") as f:
        f.write(HDR.format(title=f"`{mid}`: Theorem 3's claim of a mutant of `{b}` is false",
                           body=f"\nMutant {rec['op']} `{rec['mutant']}`. Kind {kind} ({desc}): "
                                f"{run} with {flow}, the right starts in mode {w['q0']}. Dimension {n}: the "
                                f"benchmark's bridge dimension, the last auxiliary coordinate the right clock.\n"))
        f.write("import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow\n"
                f"import RelCertifier.InstancesV2.Refute.Data.{mid}\n"
                f"import RelCertifier.InstancesV2.Cuts.{b}\n\n"
                f"namespace RelCertifier.Refute.{C}\n\n"
                "open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL\n\n"
                f"abbrev IR := Refute.{mid}_IRm\n"
                f"abbrev cX := Oracle.{b}_cutsV2X\n"
                f"abbrev w := Refute.{mid}_wit\n\n"
                f"/-- The mutant changes only the invariant: the model, hence its cut certificate, is the "
                f"suite benchmark's. -/\n"
                f"theorem same_model : IR.L = Parse.{b}_IRv2.L ∧ IR.R = Parse.{b}_IRv2.R := ⟨rfl, rfl⟩\n\n")
        if window:
            f.write("/-- Every left mode declares the same row: the claim is the window form. -/\n"
                    "theorem window_form : rowsSame IR = true := by decide +kernel\n\n")
        else:
            f.write("/-- The rows differ by mode: the claim is the mode-keyed one. -/\n"
                    "theorem keyed_form : rowsSame IR = false := by decide +kernel\n\n")
        f.write("/-- The witness's antecedent facts, decided in the kernel. -/\n")
        if window:
            f.write(f"theorem pre_ok : preOKW IR {n} cX 0 1 w = true := by decide +kernel\n\n")
        else:
            f.write(f"theorem pre_ok : preOK IR {n} cX 0 1 2 w = true := by decide +kernel\n\n")
        if kind == "A":
            f.write("/-- The broken component, decided in the kernel. -/\n"
                    f"theorem pos_ok : compPosQ IR {n} (rowOf IR w.m) w.k (witState {n} 0 2 w) = true := by\n"
                    "  decide +kernel\n\n")
        if kind == "B":
            f.write("/-- The exit facts (interior of the left envelope, the component's sign and its left Lie\n"
                    "derivative's), decided in the kernel. -/\n")
            if window:
                f.write(f"theorem b_ok : bQW IR {n} 0 1 w = true := by decide +kernel\n\n")
            else:
                f.write(f"theorem b_ok : bQ IR {n} 0 1 2 w = true := by decide +kernel\n\n")
        f.write("/-- The left and right lowerings read only their own side's coordinates (the clock\n"
                "erasure's hygiene). -/\n"
                "theorem names_ok : namesOK IR = true := by decide +kernel\n"
                f"theorem cuts_ok : cutsOK IR {n} cX = true := by decide +kernel\n\n")
        pos = "every `dt > 0`" if kind == "B" else "every `dt ≥ 0`"
        rel = "0 < dt" if kind == "B" else "0 ≤ dt"
        claim = (f"¬ windowClaim IR {n} cX cov Formula.tt 0 1 2 dt" if window else
                 f"¬ keyedClaim IR {n} cX cov Formula.tt 0 1 2 3 dt")
        f.write(f"/-- **The claim of `{mid}` is false** for every cover record (every pruning), {pos}:\n"
                f"every query group `relcert-refute-verdicts` sends is `unsat`. -/\n"
                f"theorem refuted (hv : RefVerdicts IR {n} cX w) (dt : ℝ) (hdt : {rel}) (cov : CoverEmitE) :\n"
                f"    {claim} :=\n")
        if kind == "C":
            f.write("  refute_keyed_C_clocked pre_ok rfl hv names_ok cuts_ok (by decide) (by decide) 3 (by decide)\n"
                    "    dt hdt cov\n\n")
        elif kind == "A":
            f.write("  refute_keyed_A_clocked pre_ok (by decide) pos_ok hv names_ok cuts_ok (by decide) (by decide) 3\n"
                    "    (by decide) dt hdt cov\n\n")
        elif window:
            f.write("  refute_window_B_clocked pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) 2\n"
                    "    (by decide) dt hdt cov\n\n")
        else:
            f.write("  refute_keyed_B_clocked pre_ok b_ok (by decide) hv names_ok cuts_ok (by decide) (by decide) 3\n"
                    "    (by decide) dt hdt cov\n\n")
        f.write(f"end RelCertifier.Refute.{C}\n")
    return mid, C


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--witnesses", default="docs/refute/witnesses.jsonl")
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.witnesses)]
    recs = [r for r in recs if r["witness"] and r["witness"]["kind"] in ("C", "A", "B")]
    # every mutant text first: any error stops the run before a file is written
    texts, errs = [], []
    for r in recs:
        try:
            texts.append(mutant_text(r))
        except ValueError as e:
            errs.append(str(e))
    if errs:
        print(f"gen_refute: {len(errs)} of {len(recs)} mutant texts unusable, nothing written:",
              file=sys.stderr)
        for e in errs:
            print("  " + e, file=sys.stderr)
        sys.exit(1)
    # the right mode count, from the suite benchmark's IR literal
    out, written = [], []
    for r, text in zip(recs, texts):
        src = open(f"benchmarks/suite_v2/{r['bench']}/input.txt").read()
        r["nR"] = len(re.findall(r"^\[Rsys\.mode\.", src, re.M))
        out.append((r, *emit(r, text, written)))
    with open(f"{OUT}/Table.lean", "w") as f:
        f.write(HDR.format(title="The refutation records (the runner's table)", body="\n"))
        for r, mid, C in out:
            f.write(f"import RelCertifier.InstancesV2.Refute.Data.{mid}\n")
        for b in sorted({r["bench"] for r, _, _ in out}):
            f.write(f"import RelCertifier.InstancesV2.Cuts.{b}\n")
        f.write("import RelCertifier.Checker.EvolStrengtheningX\n\n"
                "namespace RelCertifier.Refute\n\nopen RelCertifier.Parse RelCertifier.Oracle\n\n"
                "/-- A refutation's records: the mutant's IR at its bridge dimension (the Assumption 1 "
                "lemma's dimension plus one for the right clock, `bridgeDimV2`'s rule), the model's cut "
                "certificate, the witness. -/\n"
                "structure RefRec where\n  name : String\n  dim : ℕ\n  ir : PProblem\n"
                "  cuts : EvolStrengtheningX\n  wit : RefWitE\n\n"
                "def refuteTable : List RefRec := [\n")
        f.write(",\n".join(f"  ⟨\"{mid}\", {r['dim']} + 1, {mid}_IRm, {r['bench']}_cutsV2X, {mid}_wit⟩"
                           for r, mid, C in out))
        f.write(" ]\n\n")
        f.write("/-- Declared: the number of query groups over the refutations (one per right mode "
                "each). -/\n")
        f.write(f"def expectedRefuteGroups : Nat := {sum(nr_groups(r) for r, _, _ in out)}\n\n")
        f.write("end RelCertifier.Refute\n")
    with open(f"{OUT}.lean", "w") as f:
        f.write(HDR.format(title="Every kernel refutation instance", body="\n"))
        for r, mid, C in out:
            f.write(f"import RelCertifier.InstancesV2.Refute.{C}\n")
    print(f"{len(out)} refutation instances; {len(written)} mutant input(s) written")
    for p in written:
        print(f"  wrote {p}")
    mids = {mid for _, mid, _ in out}
    keep = {f"{C}.lean" for _, _, C in out} | {"Table.lean"}
    orphans = sorted([f"{MUT}/{d}" for d in os.listdir(MUT) if d not in mids] +
                     [f"{OUT}/Data/{f}" for f in os.listdir(f"{OUT}/Data")
                      if f.endswith(".lean") and f[:-5] not in mids] +
                     [f"{OUT}/{f}" for f in os.listdir(OUT) if f.endswith(".lean") and f not in keep])
    if orphans:
        print(f"gen_refute: {len(orphans)} file(s) no record produces (remove them with git rm):",
              file=sys.stderr)
        for p in orphans:
            print("  " + p, file=sys.stderr)


if __name__ == "__main__":
    main()

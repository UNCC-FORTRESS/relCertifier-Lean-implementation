#!/usr/bin/env python3
# STALE (2026-07-30 audit): this script reads a MONOLITHIC aggregator file, but the X0
# modularization moved every literal into per-benchmark leaves under
# RelCertifier/Instances/{BenchIR,BenchCovers,BenchCoversNC,EvolStrengthenings}/.
# As written it finds zero definitions and would emit an empty battery. Do not run it
# without first repointing it at the leaf directories. Kept because the emitted shapes
# below are still the reference for what those batteries contain.
"""Generate the throughout-instance battery from BenchCoversNC + BenchIR.

Per cut-free benchmark, per left window: the real cover graph at the emitted flags,
verdict-hypothesis bundles quoting the tool's exact stratified queries (identity
orders directly; non-identity full permutations through the reordered list + the
membership-permutation transport), the CoverCertM dispatch, and the per-admissible-
start window theorem (kernel decideCovered + check_sound_multi).

Validated templates: ThroughoutPilot (single node), WatertankThroughout (multi-node,
regions, dyn). This generator emits the same shapes.
"""
import re, os, sys

os.chdir(os.path.join(os.path.dirname(__file__), ".."))
nc = open("RelCertifier/Instances/BenchCoversNC.lean").read()
ir = open("RelCertifier/Instances/BenchIR.lean").read()

# ---------- parse the NC covers ----------
def parse_list(s):
    xs = [x for x in s.strip("[]").replace(" ", "").split(",") if x != ""]
    return [int(x) for x in xs]

covers = {}
for m in re.finditer(r'def (\w+)_coverNC : CoverEmitE :=\n  ⟨"(\w+)", (\[[^\]]*\]), \[\n((?:.|\n)*?)\]⟩\n', nc):
    name = m.group(1)
    body = m.group(4)
    wins = []
    for wm in re.finditer(r'⟨"(\w+)", \((\d+) : ℚ\) / (\d+), (\d+), \[(.*?)\], (\[[^\]]*\]), \[(.*?)\]⟩', body):
        mL, lamn, lamd, bud, flags_s, adm_s, strata_s = wm.groups()
        flags = []
        for fm in re.finditer(r'⟨"(\w+)", (true|false), (true|false), (true|false), (true|false), (true|false)⟩', flags_s):
            flags.append(dict(name=fm.group(1), j=fm.group(2)=="true", rp=fm.group(3)=="true",
                              rpost=fm.group(4)=="true", dp=fm.group(5)=="true", dq=fm.group(6)=="true"))
        adm = re.findall(r'"(\w+)"', adm_s)
        strata = {}
        for sm in re.finditer(r'⟨"(\w+)", (\[[0-9, ]*\]), (\[[0-9, ]*\]), (\[[0-9, ]*\])⟩', strata_s):
            strata[sm.group(1)] = (parse_list(sm.group(2)), parse_list(sm.group(3)), parse_list(sm.group(4)))
        wins.append(dict(mL=mL, lamn=int(lamn), lamd=int(lamd), bud=int(bud),
                         flags=flags, adm=adm, strata=strata))
    covers[name] = wins

# ---------- per-benchmark IR facts: stateVars, mode-name -> index ----------
ir_facts = {}
starts = [m.start() for m in re.finditer(r'def \w+_IR : PProblem :=', ir)] + [len(ir)]
for idx, m in enumerate(re.finditer(r'def (\w+)_IR : PProblem :=', ir)):
    blk = ir[starts[idx]:starts[idx+1]]
    parts = blk.split('R := {')
    sv = re.search(r'stateVars := \[([^\]]*)\]', parts[0])
    svs = re.findall(r'"(\w+)"', sv.group(1))
    lnames = re.findall(r'name := "(\w+)"', parts[0])[1:]  # drop problem name
    rnames = re.findall(r'name := "(\w+)"', parts[1]) if len(parts) > 1 else []
    ir_facts[m.group(1)] = dict(vars=svs, L=lnames, R=rnames)

def is_identity(o):
    return o == list(range(len(o)))

OBLIG = """⟨{gs}[i],
      {fL}, hostDyn vs{U} {n} Side.R (mR{U} {q}), Term.const {lam},
      strataDomHost {dom} ({gs}.take i)⟩"""

def lam_cast(w):
    return f"((({w['lamn']} : ℚ) / {w['lamd']} : ℚ) : ℝ)"


def hyp_def(kind, uname, n, l, q, lamc, gs, comps_len):
    """Emit a verdict-hypothesis Prop def for pair (l, q) of the given kind."""
    U = uname
    if kind == "seg":
        fL = f"hostDyn vs{U} {n} Side.L (mL{U} {l})"
        dom = f"(Formula.and (hostEvolve vs{U} {n} Side.L (mL{U} {l})) (hostEvolve vs{U} {n} Side.R (mR{U} {q})))"
    elif kind == "dynPre":
        fL = "(fun _ => Term.const 0)"
        dom = (f"(Formula.and (Formula.and (hostEvolve vs{U} {n} Side.L (mL{U} {l})) "
               f"(hostEvolve vs{U} {n} Side.R (mR{U} {q}))) (hostGuard vs{U} {n} Side.L (mL{U} {l})))")
    else:  # dynPost
        fL = "(fun _ => Term.const 0)"
        dom = f"(Formula.and (hostEvolve vs{U} {n} Side.L (mL{U} {l})) (hostEvolve vs{U} {n} Side.R (mR{U} {q})))"
    lam = lamc if kind == "seg" else "1"
    ob = OBLIG.format(gs=gs, fL=fL, U=U, n=n, q=q, lam=f"(Term.const {lam})".replace("Term.const (Term.const", "(Term.const").replace("))", ")") if False else lam, dom=dom)
    return (f"  ∀ i (hi : i < {gs}.length),\n"
            f"    z3solve (flowQuery {ob}) = Verdict.unsat\n"
            f"    ∨ z3solve (flowQueryStrict {ob}) = Verdict.unsat\n"
            f"    ∨ z3solve (flowQuerySuperlevel {ob}) = Verdict.unsat")

def reg_def(uname, n, l, q, post):
    U = uname
    ev = f"(Formula.and (hostEvolve vs{U} {n} Side.L (mL{U} {l})) (hostEvolve vs{U} {n} Side.R (mR{U} {q})))"
    if post:
        region = f"(Formula.and (hostGuard vs{U} {n} Side.R (mR{U} {q})) {ev})"
    else:
        region = (f"(Formula.and (Formula.and (hostGuard vs{U} {n} Side.L (mL{U} {l})) "
                  f"(hostGuard vs{U} {n} Side.R (mR{U} {q}))) {ev})")
    return (f"  ∀ g ∈ gs{U}_{l}, z3solve (Formula.and {region} "
            f"(Formula.cmp .gt g (Term.const 0))) = Verdict.unsat")

def gen_bench(name):
    wins = covers[name]
    fi = ir_facts[name]
    n = len(fi["vars"])
    U = "".join(w[0].upper() + w[1:] for w in name.split("_"))  # CamelCase tag
    vars_lit = "[" + ", ".join(f'"{v}"' for v in fi["vars"]) + "]"
    rIdx = {nm: i for i, nm in enumerate(fi["R"])}
    L = []
    L.append(f"/- GENERATED (scripts/gen_throughout.py) — do not edit. -/")
    L.append(f"import RelCertifier.Proofs.Encoding.CoverInstance")
    L.append(f"import RelCertifier.Instances.BenchCoversNC")
    L.append(f"import RelCertifier.Instances.BenchIR")
    L.append(f"")
    hb = 0 if n >= 8 else 4000000
    L.append(f"set_option maxHeartbeats {hb}")
    L.append(f"set_option linter.unnecessarySeqFocus false")
    L.append(f"")
    L.append(f"namespace RelCertifier")
    L.append(f"namespace Throughout{U}")
    L.append(f"open DL Parse")
    L.append(f"")
    L.append(f"def vs{U} : List String := {vars_lit}")
    L.append(f"def dummy{U} : Parse.PMode := ⟨\"\", [], .tt, .tt, []⟩")
    L.append(f"def mL{U} (l : ℕ) : Parse.PMode := {name}_IR.L.modes.getD l dummy{U}")
    L.append(f"def mR{U} (q : ℕ) : Parse.PMode := {name}_IR.R.modes.getD q dummy{U}")
    L.append(f"def fRow{U} (l q : ℕ) : ModeFlagsE :=")
    L.append(f"  (({name}_coverNC.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).flags.getD q")
    L.append(f"    ⟨\"\", false, false, false, false, false⟩)")
    L.append(f"noncomputable def GW{U} (l : ℕ) : SearchGraph (Var {n}) :=")
    L.append(f"  realGraphOf vs{U} {n} {name}_IR (mL{U} l)")
    L.append(f"    (({name}_coverNC.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).lamQ)")
    L.append(f"    (({name}_coverNC.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).flags)")
    L.append(f"    (fun a b => {name}_coverNC.pruned.contains (a, b))")
    L.append(f"")
    thm_names = []
    for l, w in enumerate(wins):
        gs = f"gs{U}_{l}"
        lamc = lam_cast(w)
        L.append(f"noncomputable def {gs} : List (Term (Var {n})) :=")
        L.append(f"  hostComps vs{U} {n} ((({name}_IR.invariants.find? (fun r => r.1 == \"{w['mL']}\")).getD (\"\", Parse.PForm.tt)).2)")
        L.append(f"")
        nodes = [(qn, f) for qn, f in enumerate(w["flags"]) if
                 f["j"] or f["rp"] or f["rpost"] or f["dp"] or f["dq"]]
        # node list rfl
        L.append(f"theorem GW{U}{l}_modes_eq : (GW{U} {l}).modes =")
        lamq = f"(({w['lamn']} : ℚ) / {w['lamd']})"
        L.append("    [" + ",\n     ".join(
            f"realModeOf vs{U} {n} (mL{U} {l}) {lamq} (fRow{U} {l} {qn}) (mR{U} {rIdx[f['name']]})"
            for qn, f in nodes) + "] := rfl")
        L.append(f"")
        hyps = []   # (binder name, type string)
        disp = {}   # node -> list of (fieldkind, discharge text)
        for qn, f in nodes:
            q = rIdx[f["name"]]
            so, dpo, dqo = w["strata"].get(f["name"], ([], [], []))
            gsl = gs
            def with_order(order, kind, hname):
                """Return (hyp type over the ordered list, discharge expr producing
                SegPreservesAllOn gs)."""
                if is_identity(order):
                    ht = hyp_def(kind, U, n, l, q, lamc, gsl, None)
                    return ht, None
                og = f"{gsl}Ord_{kind}_{l}_{q}"
                L.append(f"noncomputable def {og} : List (Term (Var {n})) :=")
                L.append(f"  {order}.map (fun j => {gsl}.getD j (Term.const 0))".replace("[", "([", 1).replace("]", "] : List Nat)", 1))
                L.append("")
                ht = hyp_def(kind, U, n, l, q, lamc, og, None)
                return ht, og
            if f["j"]:
                hname = f"hs_{l}_{q}"
                ht, og = with_order(so, "seg", hname)
                hyps.append((hname, ht))
                if og is None:
                    d = f"(rw [realModeOf_sys, realModeOf_dom]; exact segPresAll_from_strata_verdicts' _ _ _ _ {gsl} {hname})"
                else:
                    d = (f"(rw [realModeOf_sys, realModeOf_dom]; "
                         f"exact segPresAll_of_mem_equiv (mem_equiv_of_index_perm {gsl} _ (by decide)) "
                         f"(segPresAll_from_strata_verdicts' _ _ _ _ {og} {hname}))")
                disp.setdefault(qn, {})["segPres"] = d
            if f["rp"]:
                hname = f"hr_{l}_{q}"
                hyps.append((hname, reg_def(U, n, l, q, False)))
                disp.setdefault(qn, {})["repoPresPre"] = \
                    f"(rw [realModeOf_region]; exact regionInvAll_of_unsat' {gsl} _ (fun g hg => z3_unsat_sound ({hname} g hg)))"
            if f["rpost"]:
                hname = f"hq_{l}_{q}"
                hyps.append((hname, reg_def(U, n, l, q, True)))
                disp.setdefault(qn, {})["repoPresPost"] = \
                    f"(rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' {gsl} _ (fun g hg => z3_unsat_sound ({hname} g hg)))"
            if f["dp"]:
                hname = f"hdp_{l}_{q}"
                ht, og = with_order(dpo, "dynPre", hname)
                hyps.append((hname, ht))
                if og is None:
                    d = f"(rw [realModeOf_dynSys, realModeOf_dynDomPre]; exact segPresAll_from_strata_verdicts' _ _ _ _ {gsl} {hname})"
                else:
                    d = (f"(rw [realModeOf_dynSys, realModeOf_dynDomPre]; "
                         f"exact segPresAll_of_mem_equiv (mem_equiv_of_index_perm {gsl} _ (by decide)) "
                         f"(segPresAll_from_strata_verdicts' _ _ _ _ {og} {hname}))")
                disp.setdefault(qn, {})["repoDynPresPre"] = d
            if f["dq"]:
                hname = f"hdq_{l}_{q}"
                ht, og = with_order(dqo, "dynPost", hname)
                hyps.append((hname, ht))
                if og is None:
                    d = f"(rw [realModeOf_dynSys, realModeOf_dynDomPost]; exact segPresAll_from_strata_verdicts' _ _ _ _ {gsl} {hname})"
                else:
                    d = (f"(rw [realModeOf_dynSys, realModeOf_dynDomPost]; "
                         f"exact segPresAll_of_mem_equiv (mem_equiv_of_index_perm {gsl} _ (by decide)) "
                         f"(segPresAll_from_strata_verdicts' _ _ _ _ {og} {hname}))")
                disp.setdefault(qn, {})["repoDynPresPost"] = d
        binders = " ".join(f"({h} : {t.strip()})" for h, t in
                           [(h, t.replace(chr(10), " ")) for h, t in hyps])
        # cert theorem — six explicit field blocks, exact per-node dispatch (no `first` search)
        L.append(f"theorem cert{U}_{l} {binders} :")
        L.append(f"    CoverCertM (GW{U} {l}) {gs} := by")
        L.append(f"  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩")
        FIELDS = ["segPres", "repoPresPre", "repoPresPost", "repoDynPresPre", "repoDynPresPost"]
        for fk in FIELDS:
            L.append(f"  · intro q m hm hflag")
            L.append(f"    unfold SearchGraph.modeAt at hm")
            L.append(f"    rw [GW{U}{l}_modes_eq] at hm")
            L.append(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                L.append(f"    | {pos}, hm =>")
                L.append(f"        replace hm := Option.some.inj hm")
                L.append(f"        subst hm")
                if fk in disp.get(qn, {}):
                    L.append(f"        exact{disp[qn][fk][1:-1].replace('(rw', ' (by rw', 1) if False else ''}")
                    # emit as tactic block
                    L[-1] = f"        {disp[qn][fk][1:-1]}"
                else:
                    L.append(f"        exact absurd hflag (by simp [fRow{U}, {name}_coverNC])")
            L.append(f"    | q + {len(nodes)}, hm => simp at hm")
        L.append(f"  · intro m hm")
        L.append(f"    rw [GW{U}{l}_modes_eq] at hm")
        L.append(f"    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm")
        pats = " | ".join(["rfl"] * len(nodes))
        L.append(f"    rcases hm with {pats} <;> simp")
        L.append(f"")
        # window theorem
        fuel = w["bud"] * (len(nodes) + 1) + 1
        node_of = {f["name"]: pos for pos, (qn, f) in enumerate(nodes)}
        adm_idx = [node_of[a] for a in w["adm"]]
        hargs = " ".join(h for h, _ in hyps)
        tname = f"{name}_throughout_{w['mL']}"
        thm_names.append(tname)
        L.append(f"theorem {tname} {binders} :")
        L.append(f"    ∀ q0 ∈ {adm_idx}, ∀ ν, InvAllHolds {gs} ν →")
        L.append(f"      Covered (GW{U} {l}) ⟨q0, {w['bud']}, SrcSetting.preJ⟩")
        L.append(f"      ∧ CoexecInvAllThroughout (GW{U} {l}) {gs} ⟨q0, {w['bud']}, SrcSetting.preJ⟩ ν := by")
        L.append(f"  intro q0 hq0 ν hν")
        L.append(f"  have cert := cert{U}_{l} {hargs}")
        L.append(f"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0")
        pats = " | ".join(["rfl"] * len(adm_idx))
        L.append(f"  rcases hq0 with {pats} <;>")
        L.append(f"    exact check_sound_multi _ _ cert {fuel} _ (by decide) ν hν")
        L.append(f"")
    L.append(f"end Throughout{U}")
    L.append(f"end RelCertifier")
    return "\n".join(L) + "\n", thm_names

names = sorted(covers.keys())
if len(sys.argv) > 1:
    names = [n for n in names if n in sys.argv[1:]]
os.makedirs("RelCertifier/Instances/Throughout", exist_ok=True)
all_thms = []
for nme in names:
    txt, thms = gen_bench(nme)
    open(f"RelCertifier/Instances/Throughout/{nme}.lean", "w").write(txt)
    all_thms += thms
    print("wrote", nme, f"({len(thms)} windows)")
# umbrella
with open("RelCertifier/Instances/ThroughoutBattery.lean", "w") as f:
    f.write("/- GENERATED umbrella (scripts/gen_throughout.py) — do not edit. -/\n")
    for nme in sorted(covers.keys()):
        f.write(f"import RelCertifier.Instances.Throughout.{nme}\n")
print(f"total window theorems: {len(all_thms)}")

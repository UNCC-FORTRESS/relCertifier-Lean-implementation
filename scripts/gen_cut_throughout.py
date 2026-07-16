#!/usr/bin/env python3
"""Generate cut-lifted throughout instances (S2) from BenchCovers + EvolStrengthenings.

v1 scope: benchmarks with EMPTY left cuts and R-atom routes in
{diStrict, diNonstrict, frozen} (the arm/plant family). Frozen atoms are given a
route-A O2 residual hypothesis (domain `evR` with the own-side field; trivially UNSAT
since the atom's coordinates carry the zero field) so the generated shape is uniform;
the emission door gains these probes alongside the diStrict/diNonstrict ones.
Terrain benchmarks (shape atoms, nonempty left cuts) are generator v2.

Per benchmark, per left window: the real cover graph at the WITH-CUT emitted flags,
the node-indexed guard map `Gd` and atom lists `cutR`, verdict hypotheses quoting the
tool's cut-narrowed queries, per-atom O2 hypotheses, the CoverCertMC dispatch, and the
per-admissible-start window theorem (kernel decideCovered + check_sound_multi_cut).
"""
import re, os, sys

os.chdir(os.path.join(os.path.dirname(__file__), ".."))
cov = open("RelCertifier/Instances/BenchCovers.lean").read()
ir = open("RelCertifier/Instances/BenchIR.lean").read()
cuts_src = open("RelCertifier/Instances/EvolStrengthenings.lean").read()

def parse_list(s):
    xs = [x for x in s.strip("[]").replace(" ", "").split(",") if x != ""]
    return [int(x) for x in xs]

covers = {}
for m in re.finditer(r'def (\w+)_cover : CoverEmitE :=\n  ⟨"(\w+)", (\[[^\]]*\]), \[\n((?:.|\n)*?)\]⟩\n', cov):
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

ir_facts = {}
starts = [m.start() for m in re.finditer(r'def \w+_IR : PProblem :=', ir)] + [len(ir)]
for idx, m in enumerate(re.finditer(r'def (\w+)_IR : PProblem :=', ir)):
    blk = ir[starts[idx]:starts[idx+1]]
    parts = blk.split('R := {')
    sv = re.search(r'stateVars := \[([^\]]*)\]', parts[0])
    svs = re.findall(r'"(\w+)"', sv.group(1))
    lnames = re.findall(r'name := "(\w+)"', parts[0])[1:]
    rnames = re.findall(r'name := "(\w+)"', parts[1]) if len(parts) > 1 else []
    ir_facts[m.group(1)] = dict(vars=svs, L=lnames, R=rnames)

# ---------- parse EvolStrengthenings: benchmark -> side -> modeName -> [(atomLit, op, route)] ----------
cut_certs = {}
for m in re.finditer(r'def (\w+)_cuts : EvolStrengthening :=\n((?:.|\n)*?)\n\nexample', cuts_src):
    name, blk = m.group(1), m.group(2)
    lpart, rpart = blk.split("R := [")
    def parse_side(txt):
        out = {}
        for mm in re.finditer(r'\("(\w+)", \[(.*?)\]\)', txt, re.S):
            atoms = []
            for am in re.finditer(r'\(\((\.cmp "((?:<=)|(?:>=))" [^,]*?)\), CutRoute\.(\w+)\)', mm.group(2)):
                atoms.append(dict(lit=am.group(1), op=am.group(2), route=am.group(3)))
            out[mm.group(1)] = atoms
        return out
    cut_certs[name] = dict(L=parse_side(lpart), R=parse_side(rpart))

def is_identity(o):
    return o == list(range(len(o)))

QFORM = dict(diStrict="flowQueryStrict", diNonstrict="flowQuery",
             frozen="flowQuery", shape="flowQuerySuperlevel")
RLEM = dict(diStrict="atom_boxle_R_strict", diNonstrict="atom_boxle_R_nonstrict",
            frozen="atom_boxle_R_nonstrict", shape="atom_boxle_R_superlevel")
LLEM = dict(diStrict="atom_boxle_L_strict", diNonstrict="atom_boxle_L_nonstrict",
            frozen="atom_boxle_L_nonstrict", shape="atom_boxle_L_superlevel")

def iff_call(U, n, side, a):
    m = re.match(r'\.cmp "(<=|>=)" (\(.*?\)) (\(.*\))$', a["lit"])
    x, y = m.group(2), m.group(3)
    orc = "Or.inl rfl" if a["op"] == "<=" else "Or.inr rfl"
    return (f"exact hostAtom_iff (vars := vs{U}) (side := Side.{side}) "
            f"(x := {x}) (y := {y}) ({orc}) ν")

def fv_core(U, side, a):
    m = re.match(r'\.cmp "(<=|>=)" (\(.*?\)) (\(.*\))$', a["lit"])
    x, y = m.group(2), m.group(3)
    orc = "Or.inl rfl" if a["op"] == "<=" else "Or.inr rfl"
    other = "Lv" if side == "R" else "Rv"
    return (f"absurd (hostAtomG_fv_side (resolvesTo_{side} vs{U}) "
            f"(x := {x}) (y := {y}) ({orc}) "
            f"(by first | decide | simp [Parse.PExpr.namesFree]) "
            f"(by first | decide | simp [Parse.PExpr.namesFree]) _ h) (by simp [{other}])")

def fv_refute(U, side, a):
    return f"(fun i h => {fv_core(U, side, a)})"

def gen_bench(name):
    wins = covers[name]
    fi = ir_facts[name]
    cc = cut_certs[name]
    n = len(fi["vars"])
    U = "".join(w[0].upper() + w[1:] for w in name.split("_"))
    vars_lit = "[" + ", ".join(f'"{v}"' for v in fi["vars"]) + "]"
    rIdx = {nm: i for i, nm in enumerate(fi["R"])}
    for side in ("L", "R"):
        for rm, atoms in cc[side].items():
            assert len(atoms) <= 2, f"{name}: >2 atoms per mode"
            for a in atoms:
                assert a["route"] in ("diStrict", "diNonstrict", "frozen", "shape"), \
                    f"{name}: route {a['route']}"

    L = []
    A = L.append
    A(f"/- GENERATED (scripts/gen_cut_throughout.py) — do not edit. -/")
    A(f"import RelCertifier.Proofs.Soundness.CutCoverDischarge")
    A(f"import RelCertifier.Instances.BenchCovers")
    A(f"import RelCertifier.Instances.BenchIR")
    A(f"")
    hb = 0 if n >= 8 else 4000000
    A(f"set_option maxHeartbeats {hb}")
    A(f"set_option linter.unnecessarySeqFocus false")
    A(f"")
    A(f"namespace RelCertifier")
    A(f"namespace CutThroughout{U}")
    A(f"open DL Parse")
    A(f"")
    A(f"def vs{U} : List String := {vars_lit}")
    A(f"def dummy{U} : Parse.PMode := ⟨\"\", [], .tt, .tt, []⟩")
    A(f"def mL{U} (l : ℕ) : Parse.PMode := {name}_IR.L.modes.getD l dummy{U}")
    A(f"def mR{U} (q : ℕ) : Parse.PMode := {name}_IR.R.modes.getD q dummy{U}")
    A(f"def fRow{U} (l q : ℕ) : ModeFlagsE :=")
    A(f"  (({name}_cover.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).flags.getD q")
    A(f"    ⟨\"\", false, false, false, false, false⟩)")
    A(f"noncomputable def GW{U} (l : ℕ) : SearchGraph (Var {n}) :=")
    A(f"  realGraphOf vs{U} {n} {name}_IR (mL{U} l)")
    A(f"    (({name}_cover.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).lamQ)")
    A(f"    (({name}_cover.covers.getD l ⟨\"\", 1, 1, [], [], []⟩).flags)")
    A(f"    (fun a b => {name}_cover.pruned.contains (a, b))")
    A(f"")
    # guard-lowering kernel facts + O2 hypotheses, per R mode with atoms
    SIMPSET = (f"simp [mR{U}, {name}_IR, Run.lowerF, Run.lowerE, Run.resolveVar, "
               f"Run.parseRat, List.findIdx?, List.findIdx?.go]")
    o2 = {}   # rname -> [(hypname, type)]
    for rm in fi["R"]:
        atoms = cc["R"].get(rm, [])
        q = rIdx[rm]
        if atoms:
            A(f"theorem hsome{U}_{q} :")
            A(f"    (Run.lowerF vs{U} {n} Side.R (mR{U} {q}).guard : Option (IForm {n})).isSome = true := by")
            A(f"  {SIMPSET}")
            A(f"  decide")
            A(f"")
        hyps = []
        for ai, a in enumerate(atoms):
            hname = f"hO2{U}_{q}_{ai}"
            t = (f"z3solve ({QFORM[a['route']]} ⟨hostAtomG vs{U} {n} Side.R ({a['lit']}),\n"
                 f"      (fun _ => Term.const 0), hostDyn vs{U} {n} Side.R (mR{U} {q}), Term.const 1,\n"
                 f"      hostEvolve vs{U} {n} Side.R (mR{U} {q})⟩) = Verdict.unsat")
            hyps.append((hname, t, a))
        o2[rm] = hyps
    thm_names = []
    for l, w in enumerate(wins):
        gs = f"gs{U}_{l}"
        A(f"noncomputable def {gs} : List (Term (Var {n})) :=")
        A(f"  hostComps vs{U} {n} ((({name}_IR.invariants.find? (fun r => r.1 == \"{w['mL']}\")).getD (\"\", Parse.PForm.tt)).2)")
        A(f"")
        nodes = [(qn, f) for qn, f in enumerate(w["flags"]) if
                 f["j"] or f["rp"] or f["rpost"] or f["dp"] or f["dq"]]
        for f in [f for _, f in nodes]:
            for kind, key in (("seg", 0), ("dynPre", 1), ("dynPost", 2)):
                so = w["strata"].get(f["name"], ([], [], []))[key]
                assert is_identity(so), f"{name}/{w['mL']}/{f['name']}: non-identity strata (v2)"
        # node-indexed cut atoms + guards
        A(f"noncomputable def cutR{U}_{l} : ℕ → List (CutAtomP {n})")
        for pos, (qn, f) in enumerate(nodes):
            q = rIdx[f["name"]]
            atoms = cc["R"].get(f["name"], [])
            items = ", ".join(
                f"(hostAtomF vs{U} {n} Side.R ({a['lit']}), hostAtomG vs{U} {n} Side.R ({a['lit']}))"
                for a in atoms)
            A(f"  | {pos} => [{items}]")
        A(f"  | _ => []")
        A(f"noncomputable def Gd{U}_{l} : ℕ → Formula (Var {n})")
        for pos, (qn, f) in enumerate(nodes):
            A(f"  | {pos} => hostGuard vs{U} {n} Side.R (mR{U} {rIdx[f['name']]})")
        A(f"  | _ => Formula.tt")
        latoms = cc["L"].get(w["mL"], [])
        if latoms:
            items = ", ".join(
                f"(hostAtomF vs{U} {n} Side.L ({a['lit']}), hostAtomG vs{U} {n} Side.L ({a['lit']}))"
                for a in latoms)
            A(f"noncomputable def cutL{U}_{l} : List (CutAtomP {n}) := [{items}]")
        else:
            A(f"def cutL{U}_{l} : List (CutAtomP {n}) := []")
        A(f"")
        o2L = []
        for ai, a in enumerate(latoms):
            hname = f"hO2L{U}_{l}_{ai}"
            t = (f"z3solve ({QFORM[a['route']]} ⟨hostAtomG vs{U} {n} Side.L ({a['lit']}),\n"
                 f"      hostDyn vs{U} {n} Side.L (mL{U} {l}), (fun _ => Term.const 0), Term.const 1,\n"
                 f"      hostEvolve vs{U} {n} Side.L (mL{U} {l})⟩) = Verdict.unsat")
            o2L.append((hname, t, a))
        lamq = f"(({w['lamn']} : ℚ) / {w['lamd']})"
        A(f"theorem GW{U}{l}_modes_eq : (GW{U} {l}).modes =")
        A("    [" + ",\n     ".join(
            f"realModeOf vs{U} {n} (mL{U} {l}) {lamq} (fRow{U} {l} {qn}) (mR{U} {rIdx[f['name']]})"
            for qn, f in nodes) + "] := rfl")
        A(f"")
        # verdict hypotheses (narrowed)
        hyps = []
        disp = {}
        lamc = f"((({w['lamn']} : ℚ) / {w['lamd']} : ℚ) : ℝ)"
        for pos, (qn, f) in enumerate(nodes):
            q = rIdx[f["name"]]
            evLR = (f"(Formula.and (hostEvolve vs{U} {n} Side.L (mL{U} {l})) "
                    f"(hostEvolve vs{U} {n} Side.R (mR{U} {q})))")
            cutC = f"(Formula.and (cutF cutL{U}_{l}) (cutF (cutR{U}_{l} {pos})))"
            def routes(dom, fL, lam):
                ob = (f"⟨{gs}[i],\n      {fL}, hostDyn vs{U} {n} Side.R (mR{U} {q}), Term.const {lam},\n"
                      f"      strataDomHost {dom} ({gs}.take i)⟩")
                return (f"  ∀ i (hi : i < {gs}.length),\n"
                        f"    z3solve (flowQuery {ob}) = Verdict.unsat\n"
                        f"    ∨ z3solve (flowQueryStrict {ob}) = Verdict.unsat\n"
                        f"    ∨ z3solve (flowQuerySuperlevel {ob}) = Verdict.unsat")
            if f["j"]:
                hname = f"hs_{l}_{q}"
                dom = f"(Formula.and {evLR} {cutC})"
                hyps.append((hname, routes(dom, f"hostDyn vs{U} {n} Side.L (mL{U} {l})", lamc)))
                disp.setdefault(pos, {})["segPresC"] = (
                    f"rw [realModeOf_sys, realModeOf_dom]; "
                    f"exact segPresAll_from_strata_verdicts' _ _ _ _ {gs} {hname}")
            if f["rp"]:
                hname = f"hr_{l}_{q}"
                region = (f"(Formula.and (Formula.and (Formula.and (hostGuard vs{U} {n} Side.L (mL{U} {l})) "
                          f"(hostGuard vs{U} {n} Side.R (mR{U} {q}))) {evLR}) {cutC})")
                hyps.append((hname, f"  ∀ g ∈ {gs}, z3solve (Formula.and {region} "
                                    f"(Formula.cmp .gt g (Term.const 0))) = Verdict.unsat"))
                disp.setdefault(pos, {})["repoPresPreC"] = (
                    f"rw [realModeOf_region]; exact regionInvAll_of_unsat' {gs} _ "
                    f"(fun g hg => z3_unsat_sound ({hname} g hg))")
            if f["rpost"]:
                hname = f"hq_{l}_{q}"
                region = (f"(Formula.and (Formula.and (hostGuard vs{U} {n} Side.R (mR{U} {q})) {evLR}) {cutC})")
                hyps.append((hname, f"  ∀ g ∈ {gs}, z3solve (Formula.and {region} "
                                    f"(Formula.cmp .gt g (Term.const 0))) = Verdict.unsat"))
                disp.setdefault(pos, {})["repoPresPostC"] = (
                    f"rw [realModeOf_regionPost]; exact regionInvAll_of_unsat' {gs} _ "
                    f"(fun g hg => z3_unsat_sound ({hname} g hg))")
            if f["dp"]:
                hname = f"hdp_{l}_{q}"
                dom = (f"(Formula.and (Formula.and {evLR} (hostGuard vs{U} {n} Side.L (mL{U} {l}))) {cutC})")
                hyps.append((hname, routes(dom, "(fun _ => Term.const 0)", "1")))
                disp.setdefault(pos, {})["repoDynPresPreC"] = (
                    f"rw [realModeOf_dynSys, realModeOf_dynDomPre]; "
                    f"exact segPresAll_from_strata_verdicts' _ _ _ _ {gs} {hname}")
            if f["dq"]:
                hname = f"hdq_{l}_{q}"
                dom = f"(Formula.and {evLR} {cutC})"
                hyps.append((hname, routes(dom, "(fun _ => Term.const 0)", "1")))
                disp.setdefault(pos, {})["repoDynPresPostC"] = (
                    f"rw [realModeOf_dynSys, realModeOf_dynDomPost]; "
                    f"exact segPresAll_from_strata_verdicts' _ _ _ _ {gs} {hname}")
        # O2 hypotheses for every node with atoms
        o2_hyps = []
        for pos, (qn, f) in enumerate(nodes):
            o2_hyps += o2.get(f["name"], [])
        seen = set()
        o2_uniq = []
        for hname, t, a in o2_hyps:
            if hname not in seen:
                seen.add(hname)
                o2_uniq.append((hname, t, a))
        binders = " ".join(f"({h} : {t.strip()})" for h, t in
                           [(h, t.replace(chr(10), " ")) for h, t in hyps]
                           + [(h, t.replace(chr(10), " ")) for h, t, _ in o2_uniq]
                           + [(h, t.replace(chr(10), " ")) for h, t, _ in o2L])
        # per-atom exact blocks
        def atom_stay_R(h, lam_c, dom_imp, ind):
            hname, _, a = h
            p = " " * ind
            return [f"{p}exact {RLEM[a['route']]} _ _ _ {lam_c} (by norm_num) _ _",
                    f"{p}  {fv_refute(U, 'R', a)}",
                    f"{p}  {dom_imp} (z3_unsat_sound {hname}) hb"]
        def atom_stay_L(h, lam_t, dom_imp, ind):
            hname, _, a = h
            p = " " * ind
            return [f"{p}exact {LLEM[a['route']]} _ _ _ {lam_t} _ _",
                    f"{p}  {fv_refute(U, 'L', a)}",
                    f"{p}  {dom_imp} (z3_unsat_sound {hname}) hb"]
        def per_atom_dispatch(listdef, blocks, ind):
            """blocks: list of line-lists (relative indent), one per atom."""
            p = " " * ind
            def reind(blk, extra):
                base = len(blk[0]) - len(blk[0].lstrip())
                return [" " * extra + x[base:] for x in blk]
            out = [f"{p}simp only [{listdef}] at ha"]
            if len(blocks) == 1:
                out += [f"{p}rw [List.mem_singleton] at ha", f"{p}subst ha"] + reind(blocks[0], ind)
            else:
                out.append(f"{p}rcases List.mem_cons.mp ha with rfl | ha")
                b0 = reind(blocks[0], ind + 2)
                out.append(f"{p}· " + b0[0].strip())
                out += b0[1:]
                out.append(f"{p}· rw [List.mem_singleton] at ha")
                out.append(f"{p}  subst ha")
                out += reind(blocks[1], ind + 2)
            return out
        def stay_text(pos, f, lam_c, dom_imp, sysdom_rw):
            hlist = o2[f["name"]]
            return ([f"        {sysdom_rw}", f"        intro a ha ν hb"]
                    + per_atom_dispatch(f"cutR{U}_{l}",
                        [atom_stay_R(h, lam_c, dom_imp, 8) for h in hlist], 8))
        # cert theorem
        A(f"theorem cert{U}_{l} {binders} :")
        A(f"    CoverCertMC (GW{U} {l}) {gs} Gd{U}_{l} cutL{U}_{l} cutR{U}_{l} := by")
        A(f"  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩")
        # 1 hiffL
        if not latoms:
            A(f"  · exact atomsIff_nil")
        else:
            A(f"  · intro a ha ν")
            for ln in per_atom_dispatch(f"cutL{U}_{l}",
                    [[iff_call(U, n, "L", a)] for a in latoms], 4):
                A(ln)
        # 2 hiffR
        A(f"  · intro q")
        A(f"    match q with")
        for pos, (qn, f) in enumerate(nodes):
            atoms = cc["R"].get(f["name"], [])
            A(f"    | {pos} =>")
            A(f"        intro a ha ν")
            if not atoms:
                A(f"        simp only [cutR{U}_{l}] at ha")
                A(f"        exact absurd ha List.not_mem_nil")
            else:
                for ln in per_atom_dispatch(f"cutR{U}_{l}",
                        [[iff_call(U, n, "R", a)] for a in atoms], 8):
                    A(ln)
        A(f"    | q + {len(nodes)} =>")
        A(f"        intro a ha ν")
        A(f"        exact absurd ha List.not_mem_nil")
        # 3 stayJL
        if not latoms:
            A(f"  · intro q m hm hflag")
            A(f"    exact atomsStay_nil _ _")
        else:
            A(f"  · intro q m hm hflag")
            A(f"    unfold SearchGraph.modeAt at hm")
            A(f"    rw [GW{U}{l}_modes_eq] at hm")
            A(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                A(f"    | {pos}, hm =>")
                A(f"        replace hm := Option.some.inj hm")
                A(f"        subst hm")
                if f["j"]:
                    A(f"        simp only [realModeOf_sys, realModeOf_dom]")
                    A(f"        intro a ha ν hb")
                    for ln in per_atom_dispatch(f"cutL{U}_{l}",
                            [atom_stay_L(h, f"(Term.const {lamc})",
                                         "(by intro x h; exact h.1)", 8) for h in o2L], 8):
                        A(ln)
                else:
                    A(f"        exact absurd hflag (by simp [fRow{U}, {name}_cover])")
            A(f"    | q + {len(nodes)}, hm => simp at hm")
        # 4 stayJR
        def stay_field(flagkey, lam_c, dom_imp, sysdom_rw):
            A(f"  · intro q m hm hflag")
            A(f"    unfold SearchGraph.modeAt at hm")
            A(f"    rw [GW{U}{l}_modes_eq] at hm")
            A(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                A(f"    | {pos}, hm =>")
                A(f"        replace hm := Option.some.inj hm")
                A(f"        subst hm")
                if f[flagkey] and cc["R"].get(f["name"], []):
                    for ln in stay_text(pos, f, lam_c, dom_imp, sysdom_rw):
                        A(ln)
                elif f[flagkey]:
                    A(f"        intro a ha")
                    A(f"        exact absurd ha List.not_mem_nil")
                else:
                    A(f"        exact absurd hflag (by simp [fRow{U}, {name}_cover])")
            A(f"    | q + {len(nodes)}, hm => simp at hm")
        stay_field("j", lamc, "(by intro x h; exact h.2)",
                   "simp only [realModeOf_sys, realModeOf_dom]")
        # 5 stayDPreL
        if not latoms:
            A(f"  · intro q m hm hflag")
            A(f"    exact atomsStay_nil _ _")
        else:
            A(f"  · intro q m hm hflag")
            A(f"    unfold SearchGraph.modeAt at hm")
            A(f"    rw [GW{U}{l}_modes_eq] at hm")
            A(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                A(f"    | {pos}, hm =>")
                A(f"        replace hm := Option.some.inj hm")
                A(f"        subst hm")
                if f["dp"]:
                    A(f"        simp only [realModeOf_dynSys, realModeOf_dynDomPre]")
                    A(f"        refine atomsStay_L_frozen_dyn _ _ _ ?_")
                    A(f"        intro a ha i")
                    for ln in per_atom_dispatch(f"cutL{U}_{l}",
                            [[f"exact fun h => {fv_core(U, 'L', a)}"]
                             for a in latoms], 8):
                        A(ln)
                else:
                    A(f"        exact absurd hflag (by simp [fRow{U}, {name}_cover])")
            A(f"    | q + {len(nodes)}, hm => simp at hm")
        # 6 stayDPreR
        stay_field("dp", "(1 : ℝ)", "(by intro x h; exact h.1.2)",
                   "simp only [realModeOf_dynSys, realModeOf_dynDomPre]")
        # 7 stayDPostL
        if not latoms:
            A(f"  · intro q m hm hflag")
            A(f"    exact atomsStay_nil _ _")
        else:
            A(f"  · intro q m hm hflag")
            A(f"    unfold SearchGraph.modeAt at hm")
            A(f"    rw [GW{U}{l}_modes_eq] at hm")
            A(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                A(f"    | {pos}, hm =>")
                A(f"        replace hm := Option.some.inj hm")
                A(f"        subst hm")
                if f["dq"]:
                    A(f"        simp only [realModeOf_dynSys, realModeOf_dynDomPost]")
                    A(f"        refine atomsStay_L_frozen_dyn _ _ _ ?_")
                    A(f"        intro a ha i")
                    for ln in per_atom_dispatch(f"cutL{U}_{l}",
                            [[f"exact fun h => {fv_core(U, 'L', a)}"]
                             for a in latoms], 8):
                        A(ln)
                else:
                    A(f"        exact absurd hflag (by simp [fRow{U}, {name}_cover])")
            A(f"    | q + {len(nodes)}, hm => simp at hm")
        # 8 stayDPostR
        stay_field("dq", "(1 : ℝ)", "(by intro x h; exact h.2)",
                   "simp only [realModeOf_dynSys, realModeOf_dynDomPost]")
        # 9 entryR
        A(f"  · intro q ν hg")
        A(f"    match q with")
        for pos, (qn, f) in enumerate(nodes):
            q = rIdx[f["name"]]
            atoms = cc["R"].get(f["name"], [])
            A(f"    | {pos} =>")
            A(f"        intro a ha")
            if not atoms:
                A(f"        simp only [cutR{U}_{l}] at ha")
                A(f"        exact absurd ha List.not_mem_nil")
                continue
            for ln in per_atom_dispatch(f"cutR{U}_{l}",
                    [[f"exact hostGuard_cutAtoms_sat (a := {a['lit']}) (by decide) "
                      f"hsome{U}_{q} ν hg"]
                     for a in atoms], 8):
                A(ln)
        A(f"    | q + {len(nodes)} =>")
        A(f"        intro a ha")
        A(f"        exact absurd ha List.not_mem_nil")
        # 10-14 preservation fields
        for fk, flagkey in (("segPresC", "j"), ("repoPresPreC", "rp"), ("repoPresPostC", "rpost"),
                            ("repoDynPresPreC", "dp"), ("repoDynPresPostC", "dq")):
            A(f"  · intro q m hm hflag")
            A(f"    unfold SearchGraph.modeAt at hm")
            A(f"    rw [GW{U}{l}_modes_eq] at hm")
            A(f"    match q, hm with")
            for pos, (qn, f) in enumerate(nodes):
                A(f"    | {pos}, hm =>")
                A(f"        replace hm := Option.some.inj hm")
                A(f"        subst hm")
                if fk in disp.get(pos, {}):
                    A(f"        {disp[pos][fk]}")
                else:
                    A(f"        exact absurd hflag (by simp [fRow{U}, {name}_cover])")
            A(f"    | q + {len(nodes)}, hm => simp at hm")
        # 15 weightPos
        A(f"  · intro m hm")
        A(f"    rw [GW{U}{l}_modes_eq] at hm")
        A(f"    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm")
        pats = " | ".join(["rfl"] * len(nodes))
        A(f"    rcases hm with {pats} <;> simp")
        A(f"")
        # window theorem
        fuel = w["bud"] * (len(nodes) + 1) + 1
        node_of = {f["name"]: pos for pos, (qn, f) in enumerate(nodes)}
        adm_idx = [node_of[a] for a in w["adm"]]
        hargs = " ".join([h for h, _ in hyps] + [h for h, _, _ in o2_uniq]
                         + [h for h, _, _ in o2L])
        tname = f"{name}_cut_throughout_{w['mL']}"
        thm_names.append(tname)
        A(f"theorem {tname} {binders} :")
        cutlh = f"CutSat cutL{U}_{l} ν → " if latoms else ""
        A(f"    ∀ q0 ∈ {adm_idx}, ∀ ν, InvAllHolds {gs} ν → {cutlh}CutSat (cutR{U}_{l} q0) ν →")
        A(f"      Covered (GW{U} {l}) ⟨q0, {w['bud']}, SrcSetting.preJ⟩")
        A(f"      ∧ CoexecInvAllThroughoutG (GW{U} {l}) Gd{U}_{l} {gs} ⟨q0, {w['bud']}, SrcSetting.preJ⟩ ν := by")
        A(f"  intro q0 hq0 ν hν {'hcutL ' if latoms else ''}hcut")
        A(f"  have cert := cert{U}_{l} {hargs}")
        A(f"  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq0")
        pats = " | ".join(["rfl"] * len(adm_idx))
        A(f"  rcases hq0 with {pats} <;>")
        hl = "hcutL" if latoms else "(fun a ha => absurd ha List.not_mem_nil)"
        A(f"    exact check_sound_multi_cut _ _ _ _ _ cert {fuel} _ (by decide) ν hν")
        A(f"      {hl} hcut")
        A(f"")
    A(f"end CutThroughout{U}")
    A(f"end RelCertifier")
    return "\n".join(L) + "\n", thm_names

names = sys.argv[1:] if len(sys.argv) > 1 else \
    ["arm_chain_rung3", "arm_fidelity_high", "plant_fan_high",
     "refinement_ladder_rover_rung1_2to3", "refinement_ladder_rover_rung3_6to8",
     "refinement_ladder_rover_rung4_8to12", "rover_attitude_cone_12dof",
     "rover_dof_terrain_rung1", "rover_dof_terrain_rung2",
     "rover_dof_terrain_rung3_8d", "rover_dof_terrain_rung3",
     "story3_rollover_base_12dof", "story3_rollover_ladder_rung_a"]
os.makedirs("RelCertifier/Instances/CutThroughout", exist_ok=True)
all_thms = []
for nme in names:
    txt, thms = gen_bench(nme)
    open(f"RelCertifier/Instances/CutThroughout/{nme}.lean", "w").write(txt)
    all_thms += thms
    print("wrote", nme, f"({len(thms)} windows)")
print(f"total window theorems: {len(all_thms)}")

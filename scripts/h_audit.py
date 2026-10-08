"""H-falsification audit for the out-of-grammar benchmarks.

For each R mode: sample bases in the guard box, integrate the mode's field (RK4)
for dt = eps_R/lambda, check the endpoint lands in the guard box of self or a
declared successor, and the path stays in the evolve box. A violation at ALL
integer lambda in [lmin, lmax] = H-false candidate (with witness). No violation
at some lambda = "no counterexample found" (not a proof).
"""
import re, os, math, itertools
from fractions import Fraction as F
B="benchmarks/suite_uniform"
NUM=r'-?[\d.]+'

def parse(b):
    src=open(f"{B}/{b}/input.txt").read().split("\n")
    sv=[]; eps={"L":1.0,"R":1.0}; lmin=1.0; lmax=6.0; side=None; mode=None
    modes=[]
    for L in src:
        s=L.strip()
        if L.startswith("[Lsys"): side="L"
        if L.startswith("[Rsys"): side="R"
        m=re.match(r'\[Rsys\.mode\.(\w+)\]',L)
        if m: mode={"name":m.group(1),"ode":"","guard":"","next":[]}; modes.append(mode)
        if re.match(r'\[Lsys\.mode',L): mode=None
        if s.startswith("state_vars") and not sv:
            sv=[v.strip() for v in s.split("=")[1].strip().strip("[]").split(",")]
        if s.startswith("lambda_min"): lmin=float(s.split("=")[1])
        if s.startswith("lambda_max"): lmax=float(s.split("=")[1])
        if s.startswith("epsilon") and side: eps[side]=float(s.split("=")[1])
        if mode is not None and side=="R":
            if s.startswith("ode"): mode["ode"]=s.split("=",1)[1]
            if s.startswith("guard"): mode["guard"]=s.split("=",1)[1]
            if s.startswith("next"):
                mode["next"]=[v.strip() for v in s.split("=")[1].strip().strip("[]").split(",") if v.strip()]
        if s.startswith("evolve") and side=="R" and mode is not None and "evolve" not in mode:
            mode["evolve"]=s.split("=",1)[1]
    return sv, modes, eps["R"], lmin, lmax

def bounds(expr):
    d={}
    for m in re.finditer(rf'(\w+)\s*>=\s*({NUM})', expr):
        d.setdefault(m.group(1),[None,None])[0]=float(m.group(2))
    for m in re.finditer(rf'(\w+)\s*<=?\s*({NUM})|(\w+)\s*<\s*({NUM})', expr):
        v=m.group(1) or m.group(3); hi=m.group(2) or m.group(4)
        if hi is None: continue
        d.setdefault(v,[None,None])[1]=float(hi)
    return d

# --- tiny s-expr / infix RHS evaluator ---
def tokenize(e):
    return e.replace("("," ( ").replace(")"," ) ").split()

def parse_sexpr(toks, i=0):
    if toks[i]=="(":
        op=toks[i+1]; args=[]; i+=2
        while toks[i]!=")":
            a,i=parse_sexpr(toks,i); args.append(a)
        return (op,args), i+1
    t=toks[i]
    try: return ("num",float(t)), i+1
    except ValueError: return ("var",t), i+1

def evals(ast, env):
    k,v=ast
    if k=="num": return v
    if k=="var": return env[v]
    args=[evals(a,env) for a in v]
    if k=="+": return sum(args)
    if k=="-": return args[0]-sum(args[1:]) if len(args)>1 else -args[0]
    if k=="*":
        r=1.0
        for a in args: r*=a
        return r
    if k=="/": return args[0]/args[1]
    raise ValueError(f"op {k}")

def field_of(ode_str, sv):
    """returns dict var -> callable(env)->deriv; unlisted vars frozen"""
    fld={}
    for m in re.finditer(rf"(\w+)'\s*=\s*([^;]+);", ode_str):
        var, rhs = m.group(1), m.group(2).strip().replace("smt2:","")
        if re.fullmatch(NUM, rhs):
            c=float(rhs); fld[var]=(lambda c: lambda env: c)(c)
        elif rhs in sv:
            fld[var]=(lambda r: lambda env: env[r])(rhs)
        else:
            ast,_=parse_sexpr(tokenize(rhs))
            fld[var]=(lambda a: lambda env: evals(a, env))(ast)
    return fld

def rk4(fld, sv, x0, T, steps=64):
    x=dict(x0); h=T/steps; path=[dict(x)]
    for _ in range(steps):
        def f(st): return {v: (fld[v](st) if v in fld else 0.0) for v in sv}
        k1=f(x)
        x2={v:x[v]+h/2*k1[v] for v in sv}; k2=f(x2)
        x3={v:x[v]+h/2*k2[v] for v in sv}; k3=f(x3)
        x4={v:x[v]+h*k3[v] for v in sv};   k4=f(x4)
        x={v:x[v]+h/6*(k1[v]+2*k2[v]+2*k3[v]+k4[v]) for v in sv}
        path.append(dict(x))
    return x, path

def in_box(x, box, tol=1e-7):
    for v,(lo,hi) in box.items():
        if v not in x: continue
        if lo is not None and x[v] < lo-tol: return False
        if hi is not None and x[v] > hi+tol: return False
    return True

def samples(gbox, ebox, sv):
    axes=[]
    for v in sv:
        # Gd = envelope ∧ guard band: intersect both boxes
        glo,ghi=gbox.get(v,[None,None]); elo,ehi=ebox.get(v,[None,None])
        lo = glo if elo is None else (elo if glo is None else max(glo,elo))
        hi = ghi if ehi is None else (ehi if ghi is None else min(ghi,ehi))
        if lo is None and hi is None: axes.append([0.0])
        elif lo is None: axes.append([hi-1.0, hi])
        elif hi is None: axes.append([lo, lo+1.0])
        else: axes.append([lo,(lo+hi)/2,hi] if hi>lo else [lo])
    # cap combinatorics: full product over guard-constrained dims; for the OTHER dims,
    # sweep one at a time to its envelope corners (others at mid) — catches single-coordinate
    # envelope escapes that midpoints hide (e.g. a second-order block's overshoot corner)
    gdims=[i for i,v in enumerate(sv) if v in gbox]
    fixed=[axes[i][len(axes[i])//2] for i in range(len(sv))]
    pts=[]
    for combo in itertools.product(*[axes[i] for i in gdims]):
        p=list(fixed)
        for j,i in enumerate(gdims): p[i]=combo[j]
        pts.append({v:p[i] for i,v in enumerate(sv)})
        for i in range(len(sv)):
            if i in gdims: continue
            for corner in (axes[i][0], axes[i][-1]):
                if corner==p[i]: continue
                p2=list(p); p2[i]=corner
                pts.append({v:p2[ix] for ix,v in enumerate(sv)})
    # pairwise corners of non-guard dims (2 at a time) — the coupled-block escapes
    base=list(fixed)
    nds=[i for i in range(len(sv)) if i not in gdims]
    for ii in range(len(nds)):
        for jj in range(ii+1,len(nds)):
            for ci in (axes[nds[ii]][0], axes[nds[ii]][-1]):
                for cj in (axes[nds[jj]][0], axes[nds[jj]][-1]):
                    for combo in itertools.product(*[axes[i] for i in gdims]):
                        p=list(fixed)
                        for j,i in enumerate(gdims): p[i]=combo[j]
                        p[nds[ii]]=ci; p[nds[jj]]=cj
                        pts.append({v:p[ix] for ix,v in enumerate(sv)})
    return pts

def audit(b):
    sv, modes, epsR, lmin, lmax = parse(b)
    names=[m["name"] for m in modes]
    ebox=bounds(modes[0].get("evolve",""))
    lam_range=range(max(1,math.ceil(lmin)), math.floor(lmax)+1)
    per_lam={}
    for lam in lam_range:
        dt=epsR/lam
        viol=[]
        for q,m in enumerate(modes):
            gbox={v:bd for v,bd in bounds(m["guard"]).items() if v in sv}
            if not gbox: viol.append((q,"no guard box","")); continue
            try: fld=field_of(m["ode"], sv)
            except Exception as e:
                return ("UNAUDITABLE", f"mode {q}: {e}")
            succ=[names.index(t) for t in m["next"] if t in names]
            targets=[q]+[s for s in succ if s!=q]
            tboxes=[{v:bd for v,bd in bounds(modes[t]["guard"]).items() if v in sv} for t in targets]
            for base in samples(gbox, ebox, sv):
                end, path = rk4(fld, sv, base, dt)
                if not any(in_box(end, tb) for tb in tboxes):
                    viol.append((q, "landing", f"base={ {v:round(base[v],4) for v in gbox} } end={ {v:round(end[v],4) for v in sv if v in gbox or abs(end[v]-base[v])>1e-9} }"))
                    break
                if not all(in_box(p, ebox) for p in path):
                    viol.append((q, "staying", f"base={ {v:round(base[v],4) for v in gbox} }"))
                    break
        per_lam[lam]=viol
        if not viol: return ("OK", f"no violation at λ={lam} (dt={epsR}/{lam})")
    # violations at every lambda
    lam0=list(lam_range)[-1]
    v=per_lam[lam0][0]
    return ("H-FALSE?", f"violations at ALL λ∈{list(lam_range)}; e.g. λ={lam0} mode {v[0]} ({names[v[0]]}) {v[1]}: {v[2]}")

# the benchmarks without Lean data terms or parked
targets=["attitude_rate","endurance_orderlift_2to3","refinement_ladder_rover_rung1_2to3",
"refinement_ladder_rover_rung2_3to6","refinement_ladder_rover_rung2_6dof",
"refinement_ladder_rover_rung2b_6dof","refinement_ladder_rover_rung2c_6dof",
"refinement_ladder_rover_rung3_6to8","refinement_ladder_rover_rung4_8to12",
"rover3tier_rung12","rover_4d_box","rover_attitude_cone_12dof",
"rover_dof_terrain_rung1","rover_dof_terrain_rung2","rover_dof_terrain_rung3",
"rover_dof_terrain_rung3_8d","rover_drag","rover_tier_r1","shield_unreachable",
"story1_attdist_rung_a_6to8","story1_attdist_rung_b_12dof","story2_lateral_rung_a_8dof",
"story2_lateral_rung_b_12dof","story3_rollover_base_12dof","story3_rollover_ladder_rung_a",
"story3_rollover_ladder_rung_b",
# parked exp-bound five, as sanity check (expect OK):
"watertank","match_multi_rate","rover3tier_M1","robot_braking"]
for b in targets:
    try:
        verdict, msg = audit(b)
    except Exception as e:
        verdict, msg = "SCRIPT-ERR", str(e)[:80]
    print(f"{verdict:12s} {b:40s} {msg[:130]}")

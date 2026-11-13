#!/usr/bin/env python3
"""Numerical SOS (Putinar) prover for ONE printed relCertifier flow query, producing a certificate for
`sos_check.py` (`docs/SOS-ORACLE.md`). The query is the tool's own script (a level of `checkSeg` /
`checkDynRepo`, already sliced by the tool when the knob is set), `(assert (and h_1 ... h_k goal))`.
It searches, with cvxpy/Clarabel, for

    -gdot(y) - eps  =  s_0(y) + sum_i s_i(y) h_i(y) + sum_j q_j(y) e_j(y)

over the variables of the goal and of the coupled (multi-variable) hypotheses, each rescaled to
[-1, 1] from its box when the query bounds it on both sides (x = c + w y), the h_i the coupled
inequality atoms, the box products (x - lo)(hi - x) of the two-sided variables and the single
one-sided atoms, the e_j the equality atoms; eps = SOS_EPS (1e-7) when the goal is `>=` (route B),
0 otherwise; multiplier degrees as in the probe (`sos_query.py`: D = max(4, even degree of the
target), s_i of degree D - deg h_i). The certificate (JSON) carries the bases, Gram matrices and
multipliers with the justification of every hypothesis (atom index, product, or box variable); the
exact checker decides. Numerical evidence only: never a verdict by itself.

Usage: sos_prove.py QUERY.smt2 CERT.json [--budget SECONDS] [--maxbasis N] [--deg D]
Output: one line `SOS <found|unknown> ...stats`; exit 0. The certificate is written only when found.
"""
import os, sys, re, json, time, itertools, signal
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sos_check import parse_query, padd, pscale, pmul, psubst

class Budget(Exception): pass

def prove(query_text, budget=120.0, maxbasis=600, deg=0, eps_strict=Fraction(1, 10 ** 7), margin_cap=1.0):
    import numpy as np, scipy.sparse as sps
    t0 = time.time()
    stats = {}
    names, hyps, goal = parse_query(query_text)
    nv = len(names); gk, gpoly = goal
    if gk == "eq": return "unknown", None, dict(note="goal is an equality")
    strict = gk == "ge"
    eps = eps_strict if strict else Fraction(0)
    varsof = lambda p: {i for m in p for i, e in enumerate(m) if e}
    tv = varsof(gpoly)
    if not tv: return "unknown", None, dict(note="goal has no variables")
    keep = set(tv)
    for k, h in hyps:
        if len(varsof(h)) > 1: keep |= varsof(h)
    # the bounds of each kept variable from the single-variable linear atoms
    lo_b, hi_b, lo_i, hi_i = {}, {}, {}, {}
    for idx, (k, h) in enumerate(hyps):
        if k == "eq" or not h: continue
        vs_ = varsof(h)
        if len(vs_) != 1 or any(sum(m) > 1 for m in h): continue
        i = next(iter(vs_)); m1 = tuple(1 if j == i else 0 for j in range(nv))
        a = h.get(m1, 0); b = h.get((0,) * nv, 0)
        if a > 0:
            if i not in lo_b or -b / a > lo_b[i]: lo_b[i], lo_i[i] = -b / a, idx
        elif a < 0:
            if i not in hi_b or -b / a < hi_b[i]: hi_b[i], hi_i[i] = -b / a, idx
    kv = sorted(keep); cidx = {i: j for j, i in enumerate(kv)}; ny = len(kv)
    cmap = {}; maps = []
    for i in range(nv):
        if i not in cidx: maps.append(None); continue
        if i in lo_b and i in hi_b and hi_b[i] > lo_b[i]:
            lo, hi = lo_b[i], hi_b[i]; c, w = (lo + hi) / 2, (hi - lo) / 2
            cmap[names[i]] = dict(lo=str(lo), hi=str(hi))
        else:
            c = lo_b.get(i, hi_b.get(i, Fraction(0))); w = Fraction(1)
            cmap[names[i]] = dict(c=str(c), w=str(w))
        m = [0] * ny; m[cidx[i]] = 1
        maps.append({(0,) * ny: c, tuple(m): w})
    # a hypothesis over a dropped variable cannot be used; substitute the kept ones only
    for i in range(nv):
        if maps[i] is None:
            m = [0] * ny; maps[i] = {tuple(m): Fraction(0)}       # placeholder, never used (filtered below)
    sub = lambda p: psubst(p, ny, maps)
    target = padd(pscale(sub(gpoly), -1), {(0,) * ny: -eps})
    ineq = []     # (justification, poly in y)
    for idx, (k, h) in enumerate(hyps):
        vs_ = varsof(h)
        if not vs_ or not vs_ <= keep: continue
        if k == "eq": continue
        if len(vs_) == 1:
            i = next(iter(vs_))
            if i in lo_b and i in hi_b and hi_b[i] > lo_b[i]: continue      # covered by the box product below
        ineq.append((dict(atom=idx), sub(h)))
    for i in kv:
        if i in lo_b and i in hi_b and hi_b[i] > lo_b[i]:
            y = [0] * ny; y[cidx[i]] = 2
            ineq.append((dict(box=names[i]), {(0,) * ny: Fraction(1), tuple(y): Fraction(-1)}))
    eqs = [(dict(atom=idx), sub(h)) for idx, (k, h) in enumerate(hyps) if k == "eq" and varsof(h) and varsof(h) <= keep]
    ineq = [(j, p) for j, p in ineq if p]; eqs = [(j, p) for j, p in eqs if p]
    tdeg = max((sum(m) for m in target), default=0)
    D = deg or max(4, tdeg + (tdeg % 2))
    def monos(d): return [m for m in itertools.product(range(d + 1), repeat=ny) if sum(m) <= d]
    ms0 = monos(D // 2); nb = len(ms0)
    stats.update(vars=ny, hyps=len(ineq) + len(eqs), deg=D, basis=nb, strict=int(strict))
    if nb > maxbasis: return "unknown", None, dict(stats, note=f"basis {nb} > cap {maxbasis}")
    allm = monos(D); idx = {m: i for i, m in enumerate(allm)}; M = len(allm)
    import cvxpy as cp
    blocks = []; terms = []
    # every Gram matrix is Qt + t I with Qt PSD and t >= 0 maximized: a uniform margin t > 0 keeps the
    # rounded matrices positive definite, so the exact check can absorb the rounding residual
    tvar = cp.Variable(name="t")
    def gram_block(name, basis, poly):
        nbk = len(basis); r, c, d = [], [], []
        pt = list(poly.items()) if poly is not None else [((0,) * ny, Fraction(1))]
        for a, ma in enumerate(basis):
            for b, mb in enumerate(basis):
                base = tuple(x + y for x, y in zip(ma, mb))
                for mono, cf in pt:
                    key = tuple(x + z for x, z in zip(base, mono))
                    if key not in idx: raise ValueError("degree overflow")
                    r.append(idx[key]); c.append(a + nbk * b); d.append(float(cf))
        A = sps.csr_matrix((d, (r, c)), shape=(M, nbk * nbk))
        Q = cp.Variable((nbk, nbk), PSD=True, name=name)
        blocks.append((name, Q, A, basis))
        ivec = np.eye(nbk).reshape(-1, order="F")
        terms.append(A @ (cp.reshape(Q, (nbk * nbk,), order="F") + tvar * ivec))
    gram_block("Q0", ms0, None)
    used_ineq = []
    for i, (j, p) in enumerate(ineq):
        dm = D - max(sum(m) for m in p)
        if dm < 0: continue
        gram_block(f"S{i}", monos(dm // 2), p); used_ineq.append(i)
    lams = []; used_eq = []
    for j, (ju, p) in enumerate(eqs):
        dm = max(D - max(sum(m) for m in p), 0); msq = monos(dm); r, c, d = [], [], []
        for k2, mk in enumerate(msq):
            for mono, cf in p.items():
                key = tuple(x + y for x, y in zip(mk, mono))
                if key not in idx: continue
                r.append(idx[key]); c.append(k2); d.append(float(cf))
        E = sps.csr_matrix((d, (r, c)), shape=(M, len(msq))); lam = cp.Variable(len(msq), name=f"L{j}")
        lams.append((f"L{j}", lam, E, msq)); terms.append(E @ lam); used_eq.append(j)
    t = np.zeros(M)
    for mono, cf in target.items(): t[idx[mono]] += float(cf)
    used = sorted(set(itertools.chain.from_iterable(A.nonzero()[0] for _, _, A, _ in blocks)) | set(itertools.chain.from_iterable(E.nonzero()[0] for _, _, E, _ in lams)) | set(np.nonzero(t)[0]))
    R = sps.csr_matrix((np.ones(len(used)), (range(len(used)), used)), shape=(len(used), M))
    cons = [R @ sum(terms) == R @ t, tvar >= 0, tvar <= margin_cap]
    stats.update(sdp_cons=len(used), build_s=round(time.time() - t0, 1))
    prob = cp.Problem(cp.Maximize(tvar), cons)
    limit = max(5.0, budget - (time.time() - t0) - 2)
    try:
        prob.solve(solver="CLARABEL", verbose=False, time_limit=limit)
    except Budget:
        raise
    except Exception as ex:
        return "unknown", None, dict(stats, note=f"solver error {type(ex).__name__}: {str(ex)[:80]}")
    st = prob.status
    stats.update(solver_status=st, t=round(time.time() - t0, 1))
    if st not in ("optimal", "optimal_inaccurate"):
        return "unknown", None, stats
    vals = {}; acc = np.zeros(M); tm = float(tvar.value)
    stats.update(margin=tm)
    for name, Q, A, basis in blocks:
        V = np.asarray(Q.value) + tm * np.eye(len(basis)); V = (V + V.T) / 2; vals[name] = V; acc += A @ V.reshape(-1, order="F")
    for name, lam, E, msq in lams:
        V = np.asarray(lam.value).reshape(-1); vals[name] = V; acc += E @ V
    stats.update(residual=float(np.max(np.abs(acc - t))), mineig=float(min(np.linalg.eigvalsh(vals[n]).min() for n, _, _, _ in blocks)))
    cert = dict(vars=[names[i] for i in kv], map=cmap, eps=str(eps), degree=D,
                s0=dict(basis=[list(m) for m in ms0], gram=vals["Q0"].tolist()), mult=[], eq=[])
    for i in used_ineq:
        name, Q, A, basis = next(b for b in blocks if b[0] == f"S{i}")
        cert["mult"].append(dict(just=ineq[i][0], basis=[list(m) for m in basis], gram=vals[name].tolist()))
    for j in used_eq:
        name, lam, E, msq = next(l for l in lams if l[0] == f"L{j}")
        cert["eq"].append(dict(just=eqs[j][0], basis=[list(m) for m in msq], coeffs=vals[name].tolist()))
    return "found", cert, stats

def fmt(stats):
    return " ".join(f"{k}={v:.1e}" if isinstance(v, float) else f"{k}={v}" for k, v in stats.items())

def main(argv):
    if len(argv) < 3: sys.stderr.write(__doc__); return 2
    budget = 120.0; maxbasis = 600; deg = 0
    args = argv[1:]
    while len(args) > 2:
        if args[-2] == "--budget": budget = float(args[-1]); args = args[:-2]
        elif args[-2] == "--maxbasis": maxbasis = int(args[-1]); args = args[:-2]
        elif args[-2] == "--deg": deg = int(args[-1]); args = args[:-2]
        else: break
    qpath, cpath = args[0], args[1]
    def alarm(signum, frame): raise Budget()
    signal.signal(signal.SIGALRM, alarm); signal.alarm(int(budget) + 5)
    try:
        status, cert, stats = prove(open(qpath).read(), budget, maxbasis, deg)
    except Budget:
        print("SOS unknown note=budget"); return 0
    except Exception as ex:
        print(f"SOS unknown note=error:{type(ex).__name__}:{str(ex)[:80]}"); return 0
    if cert is not None:
        json.dump(cert, open(cpath, "w"))
    print(f"SOS {status} {fmt(stats)}"); return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))

#!/usr/bin/env python3
"""Exact checker of an SOS (Putinar) certificate for ONE printed relCertifier flow query
(`docs/SOS-ORACLE.md`). The query is the tool's own script, `(assert (and h_1 ... h_k goal))` with the
goal `(> gdot 0)` (routes A, C) or `(>= gdot 0)` (route B, preceded by the boundary atom `(= g 0)`).
A certificate is the numerical output of `sos_prove.py` (or of the probe's `sos_phase1.py`): bases
and Gram matrices of the multipliers of the identity

    -gdot(y) - eps  =  s_0(y) + sum_i s_i(y) h_i(y) + sum_j q_j(y) e_j(y)        (all polynomials in y)

where x_v = c_v + w_v y_v is an affine change of variables (w_v > 0), h_i ranges over hypothesis atoms
of the query (`h >= 0`, a strict `h > 0` weakened to `>= 0`), products of two of them, or a box product
(x - lo)(hi - x) whose bounds are EXACTLY the tightest single-variable bounds among the query's atoms,
e_j over the equality atoms, s_0 and s_i are Gram forms b^T G b with G positive semidefinite, and q_j is
a free polynomial. Every Gram entry and coefficient is rounded to a rational; the identity is then
checked EXACTLY over Q: the residual (target minus right-hand side) is absorbed into s_0's Gram matrix
(a monomial of the residual must be a product of two basis monomials, else REJECTED) and every Gram
matrix, s_0's after absorption, is checked positive semidefinite by an exact rational LDL^T (a negative
pivot, or a zero pivot with a nonzero column, is REJECTED). A multiplier whose hypothesis is not
justified by the query (a box the query does not bound on both sides, an atom index out of range, an
atom that is an equality used as an inequality) is DROPPED, not trusted; the identity must then still
close through the residual absorption. VERIFIED means: the exact identity holds with every multiplier
justified, hence every real state satisfying the hypotheses has -gdot >= eps, contradicting the goal
atom (eps > 0 is required when the goal is `>=`), so the query is unsatisfiable.

Usage: sos_check.py QUERY.smt2 CERT.json            (sos_prove.py's certificate)
       sos_check.py --phase1 DIR                     (the probe's logs/sos_certs/<id>/: cert.npz, meta.json, query.smt2)
Output: one line `VERIFIED ...stats` or `REJECTED <reason>`; exit 0 either way, 2 on a usage/parse error.
"""
import sys, os, re, json, time, itertools
from fractions import Fraction

# ---------------------------------------------------------------- query parsing (z3's parser, exact rationals)
def strip_script(text):
    return re.sub(r"\(echo[^\n]*\n|\(reset\)\n|\(set-option[^\n]*\n|\(check-sat\)\n", "", text)

def parse_query(text):
    """Returns (vars, hyps, goal): hyps a list of (kind, poly) with kind in {ge, gt, eq} and poly a dict
    {exponent tuple: Fraction} over `vars` (sorted names); goal the last atom. Strict `gt` atoms are kept as such
    (used as `ge`, a weakening)."""
    import z3
    fs = z3.parse_smt2_string(strip_script(text))
    def atoms(f):
        if z3.is_and(f):
            out = []
            for c in f.children(): out += atoms(c)
            return out
        return [f]
    ats = []
    for f in fs: ats += atoms(f)
    names = sorted({str(v) for a in ats for v in z3.z3util.get_vars(a)})
    idx = {v: i for i, v in enumerate(names)}
    nv = len(names)
    def to_poly(e, cache={}):
        k = e.get_id()
        if k in cache: return cache[k]
        if z3.is_rational_value(e):
            r = {(0,) * nv: Fraction(e.numerator_as_long(), e.denominator_as_long())}
        elif z3.is_int_value(e):
            r = {(0,) * nv: Fraction(e.as_long())}
        elif z3.is_const(e):
            m = [0] * nv; m[idx[str(e)]] = 1; r = {tuple(m): Fraction(1)}
        else:
            d = e.decl().kind(); ch = [to_poly(c) for c in e.children()]
            if d == z3.Z3_OP_ADD:
                r = {}
                for c in ch: r = padd(r, c)
            elif d == z3.Z3_OP_SUB:
                r = ch[0] if len(ch) > 1 else pscale(ch[0], -1)
                for c in ch[1:]: r = padd(r, pscale(c, -1))
            elif d == z3.Z3_OP_MUL:
                r = {(0,) * nv: Fraction(1)}
                for c in ch: r = pmul(r, c)
            elif d == z3.Z3_OP_DIV:
                den = ch[1]
                if set(den) - {(0,) * nv}: raise ValueError("division by a non-constant")
                r = pscale(ch[0], 1 / den[(0,) * nv])
            elif d == z3.Z3_OP_UMINUS: r = pscale(ch[0], -1)
            elif d == z3.Z3_OP_TO_REAL: r = ch[0]
            elif d == z3.Z3_OP_POWER:
                ex = ch[1]
                if set(ex) - {(0,) * nv}: raise ValueError("non-constant exponent")
                n = ex[(0,) * nv]
                if n.denominator != 1 or n < 0: raise ValueError("non-natural exponent")
                r = {(0,) * nv: Fraction(1)}
                for _ in range(int(n)): r = pmul(r, ch[0])
            else: raise ValueError(f"op {e.decl().name()}")
        cache[k] = r
        return r
    rows = []
    for a in ats:
        neg = False
        while z3.is_not(a): a = a.children()[0]; neg = not neg
        if z3.is_true(a):
            if neg: raise ValueError("atom false")
            continue
        if z3.is_false(a):
            if neg: continue
            raise ValueError("atom false")
        k = a.decl().kind(); l, r = a.children(); le, re_ = to_poly(l), to_poly(r)
        if neg: k = {z3.Z3_OP_LE: z3.Z3_OP_GT, z3.Z3_OP_GE: z3.Z3_OP_LT, z3.Z3_OP_LT: z3.Z3_OP_GE, z3.Z3_OP_GT: z3.Z3_OP_LE}[k]
        diff = padd(le, pscale(re_, -1)); ndiff = pscale(diff, -1)
        if k == z3.Z3_OP_LE: rows.append(("ge", ndiff))
        elif k == z3.Z3_OP_GE: rows.append(("ge", diff))
        elif k == z3.Z3_OP_LT: rows.append(("gt", ndiff))
        elif k == z3.Z3_OP_GT: rows.append(("gt", diff))
        elif k == z3.Z3_OP_EQ: rows.append(("eq", diff))
        else: raise ValueError(f"atom {a}")
    if not rows: raise ValueError("empty query")
    return names, rows[:-1], rows[-1]

# ---------------------------------------------------------------- exact sparse polynomials {exponent tuple: Fraction}
def padd(a, b):
    r = dict(a)
    for m, c in b.items():
        v = r.get(m, 0) + c
        if v == 0: r.pop(m, None)
        else: r[m] = v
    return r

def pscale(a, s):
    s = Fraction(s)
    return {} if s == 0 else {m: c * s for m, c in a.items()}

def pmul(a, b):
    r = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb)); v = r.get(m, 0) + ca * cb
            if v == 0: r.pop(m, None)
            else: r[m] = v
    return r

def psubst(p, nv_new, maps):
    """Substitute variable i by the affine poly maps[i] (a poly over the new variables)."""
    r = {}
    pw_cache = {}
    def power(i, k):
        key = (i, k)
        if key not in pw_cache:
            q = {(0,) * nv_new: Fraction(1)}
            for _ in range(k): q = pmul(q, maps[i])
            pw_cache[key] = q
        return pw_cache[key]
    for m, c in p.items():
        t = {(0,) * nv_new: c}
        for i, k in enumerate(m):
            if k: t = pmul(t, power(i, k))
        r = padd(r, t)
    return r

def gram_form(basis, G):
    """b^T G b as a poly; basis a list of exponent tuples, G a square list of Fractions."""
    r = {}
    n = len(basis)
    for a in range(n):
        for b in range(n):
            g = G[a][b]
            if g == 0: continue
            m = tuple(x + y for x, y in zip(basis[a], basis[b])); v = r.get(m, 0) + g
            if v == 0: r.pop(m, None)
            else: r[m] = v
    return r

def to_frac(x, den=1 << 40):
    """Round a float to a dyadic rational."""
    return Fraction(int(round(float(x) * den)), den)

def ldl_psd(G):
    """Exact LDL^T over Q. Returns (ok, min pivot, reason)."""
    n = len(G)
    A = [row[:] for row in G]
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    minp = None
    for k in range(n):
        d = A[k][k] - sum(L[k][j] * L[k][j] * D[j] for j in range(k) if D[j] != 0)
        if d < 0: return False, d, f"negative pivot {float(d):.3e} at {k}"
        D[k] = d
        minp = d if minp is None else min(minp, d)
        for i in range(k + 1, n):
            s = A[i][k] - sum(L[i][j] * L[k][j] * D[j] for j in range(k) if D[j] != 0)
            if d == 0:
                if s != 0: return False, Fraction(0), f"zero pivot at {k} with nonzero column entry {float(s):.3e}"
                L[i][k] = Fraction(0)
            else:
                L[i][k] = s / d
    return True, minp if minp is not None else Fraction(0), ""

# ---------------------------------------------------------------- certificate formats
def load_json_cert(path):
    return json.load(open(path))

def load_phase1(d):
    """The probe's format (sos_phase1.py): cert.npz (Q0, S<i>, L<j> and their bases over meta['vars']) and
    meta.json (vars, box, eps, degree, ineq[i] = {block, kind, original}, eq[j] = {block, original}). Box multipliers
    are the entries with kind 'box'; their variable is read from the block's `original` text `1 - y_<v>**2`."""
    import numpy as np
    meta = json.load(open(os.path.join(d, "meta.json")))
    z = np.load(os.path.join(d, "cert.npz"))
    vs = meta["vars"]
    cert = dict(vars=vs, eps=str(meta["eps"]), degree=meta["degree"],
                map={v: dict(lo=meta["box"][v][0], hi=meta["box"][v][1]) for v in vs}, mult=[], eq=[])
    cert["s0"] = dict(basis=z["basis_Q0"].tolist(), gram=z["Q0"].tolist())
    for i, h in enumerate(meta["ineq"]):
        blk = h["block"]
        if blk not in z.files: continue
        if h["kind"] == "box":
            m = re.match(r"1 - y_(\S+)\*\*2", h["original"])
            just = dict(box=m.group(1))
        elif h["kind"] in ("box_lo", "box_hi"):
            # one-sided: y + 1 = (x - lo)/w, resp. 1 - y = (hi - x)/w
            m = re.match(r"(?:y_(\S+) \+ 1|1 - y_(\S+))$", h["original"])
            just = dict(bound=m.group(1) or m.group(2), side="lo" if h["kind"] == "box_lo" else "hi")
        else:
            just = dict(poly=h["original"])
        cert["mult"].append(dict(just=just, basis=z["basis_" + blk].tolist(), gram=z[blk].tolist()))
    for j, e in enumerate(meta["eq"]):
        blk = e["block"]
        cert["eq"].append(dict(just=dict(poly=e["original"]), basis=z["basis_" + blk].tolist(), coeffs=z[blk].tolist()))
    query = open(os.path.join(d, "query.smt2")).read()
    return query, cert

# ---------------------------------------------------------------- the check
def sympy_poly_to_dict(text, names):
    """A polynomial given as text in the original variables (the probe's `original` strings) as an exact dict."""
    import sympy as sp
    syms = {v: sp.Symbol(v) for v in names}
    e = sp.sympify(text, locals=syms, rational=True)
    P = sp.Poly(sp.expand(e), *[syms[v] for v in names], domain="QQ")
    return {m: Fraction(int(c.p), int(c.q)) for m, c in zip(P.monoms(), P.coeffs())}

def match_atom(poly, hyps, kinds=("ge", "gt")):
    """The index of a hypothesis atom equal to `poly` up to a POSITIVE rational factor, and the factor, or None."""
    if not poly: return None
    m0 = next(iter(poly))
    for i, (k, h) in enumerate(hyps):
        if k not in kinds or not h or m0 not in h: continue
        f = poly[m0] / h[m0]
        if f <= 0 and "eq" not in kinds: continue
        if pscale(h, f) == poly: return i, f
    return None

def check(query_text, cert, verbose=False):
    t0 = time.time()
    names, hyps, goal = parse_query(query_text)
    nv = len(names); gk, gpoly = goal
    if gk == "eq": return "REJECTED goal atom is an equality"
    strict_goal = gk == "ge"                      # route B: the negated goal is gdot >= 0; we need -gdot >= eps > 0
    eps = Fraction(cert.get("eps", "0"))
    if eps < 0: return "REJECTED eps < 0"
    if strict_goal and eps <= 0: return "REJECTED goal is `>=` but eps = 0"
    # the change of variables x_v = c_v + w_v y_v over the certificate's variables (unlisted variables stay themselves)
    cvars = list(cert["vars"])
    if any(v not in names for v in cvars): return "REJECTED certificate variable not in the query: " + ", ".join(v for v in cvars if v not in names)
    ny = len(cvars); cidx = {v: i for i, v in enumerate(cvars)}
    # bounds per variable from the single-variable linear atoms (box justification, point variables)
    lo_b, hi_b = {}, {}
    for k, h in hyps:
        if k == "eq" or not h: continue
        vs_ = {i for m in h for i, e in enumerate(m) if e}
        if len(vs_) != 1 or any(sum(m) > 1 for m in h): continue
        i = next(iter(vs_)); m1 = tuple(1 if j == i else 0 for j in range(nv))
        a = h.get(m1, 0); b = h.get((0,) * nv, 0)   # a x + b >= 0
        if a > 0: lo_b[i] = max(lo_b.get(i, -b / a), -b / a)
        elif a < 0: hi_b[i] = min(hi_b.get(i, -b / a), -b / a)
    maps = []
    point = set()        # certificate variables the query pins to a point (lo = hi): x = c, y_v := 0
    for i, v in enumerate(names):
        if v in cidx:
            mp = cert["map"][v]
            if "lo" in mp:
                lo, hi = Fraction(mp["lo"]), Fraction(mp["hi"])
                if hi < lo: return f"REJECTED box of {v} is empty"
                if hi == lo:
                    # a point: sound only when the query's own bounds pin x to it; then every
                    # occurrence of y_v is instantiated at 0 (a restriction of an SOS is an SOS)
                    if not (i in lo_b and i in hi_b and lo_b[i] >= lo and hi_b[i] <= hi):
                        return f"REJECTED {v} mapped to the point {lo} the query does not pin it to"
                    point.add(cidx[v]); c, w = lo, Fraction(0)
                else:
                    c, w = (lo + hi) / 2, (hi - lo) / 2
            else:
                c, w = Fraction(mp["c"]), Fraction(mp["w"])
                if w <= 0: return f"REJECTED scale of {v} not positive"
            m = [0] * ny; m[cidx[v]] = 1
            maps.append({(0,) * ny: c, tuple(m): w} if w != 0 else {(0,) * ny: c})
        else:
            maps.append(None)
    unlisted = [names[i] for i in range(nv) if maps[i] is None]
    if unlisted:
        # keep unlisted variables as extra y-variables (identity map) so the residual exposes them
        extra = {v: ny + k for k, v in enumerate(unlisted)}; ny2 = ny + len(unlisted)
        maps2 = []
        for i, v in enumerate(names):
            if maps[i] is not None:
                maps2.append({tuple(list(m) + [0] * len(unlisted)): c for m, c in maps[i].items()})
            else:
                m = [0] * ny2; m[extra[v]] = 1; maps2.append({tuple(m): Fraction(1)})
        maps = maps2; ny = ny2
    def pad(basis):
        return [tuple(list(m) + [0] * (ny - len(m))) for m in basis]
    def restrict(basis, G):
        """Instantiate the point variables at 0: keep the basis monomials free of them and the
        corresponding principal submatrix of the Gram matrix (PSD is preserved)."""
        if not point: return basis, G
        keep = [a for a, m in enumerate(basis) if all(m[j] == 0 for j in point)]
        return [basis[a] for a in keep], [[G[a][b] for b in keep] for a in keep]
    def project_psd(G, tol=1e-5):
        """A multiplier Gram with a slightly negative spectrum (the solver's tolerance) is projected
        onto the PSD cone before rounding; the identity's residual is then absorbed into s_0."""
        import numpy as np
        A = np.array(G, dtype=float); A = (A + A.T) / 2
        w, U = np.linalg.eigh(A)
        if w.min() >= 0 or w.min() < -tol: return G, float(w.min()), False
        # clip, then a diagonal shift of 2^-30 so the rounded matrix is positive definite; the
        # shift is paid by the residual (absorbed into s_0)
        w2 = np.clip(w, 0, None) + 2.0 ** -30
        return ((U * w2) @ U.T).tolist(), float(w.min()), True
    sub = lambda p: psubst(p, ny, maps)
    hy = [(k, sub(h)) for k, h in hyps]
    target = padd(pscale(sub(gpoly), -1), {(0,) * ny: -eps})
    # right-hand side
    rhs = {}
    dropped = []
    s0 = cert["s0"]
    if len(s0["gram"]) != len(s0["basis"]) or any(len(r) != len(s0["basis"]) for r in s0["gram"]):
        return "REJECTED s0 Gram/basis size mismatch"
    b0, G0f = restrict(pad(s0["basis"]), s0["gram"])
    G0 = [[to_frac(x) for x in row] for row in G0f]
    n0 = len(b0)
    for a in range(n0):
        for b in range(a + 1, n0):
            G0[a][b] = G0[b][a] = (G0[a][b] + G0[b][a]) / 2
    rhs = padd(rhs, gram_form(b0, G0))
    nmult = 0; nproj = 0
    for mi, mult in enumerate(cert.get("mult", [])):
        just = mult["just"]
        if "box" in just:
            v = just["box"]
            if v not in cidx or v not in names: dropped.append(f"box {v}: unknown variable"); continue
            i = names.index(v); mp = cert["map"][v]
            if "lo" not in mp: dropped.append(f"box {v}: no box in the map"); continue
            lo, hi = Fraction(mp["lo"]), Fraction(mp["hi"])
            if cidx[v] in point:
                # y_v := 0 turns the certificate's 1 - y_v^2 into the constant 1
                hpoly = {(0,) * ny: Fraction(1)}; scale = Fraction(1)
            else:
                if lo_b.get(i) != lo or hi_b.get(i) != hi:
                    dropped.append(f"box {v}=[{lo},{hi}] not the query's bounds [{lo_b.get(i)},{hi_b.get(i)}]"); continue
                # (x - lo)(hi - x) = w^2 (1 - y^2) with x = c + w y: the multiplier of 1 - y^2 is w^2 times that of the product
                m1 = tuple(1 if j == i else 0 for j in range(nv))
                hpoly = sub(pmul({m1: Fraction(1), (0,) * nv: -lo}, {m1: Fraction(-1), (0,) * nv: hi}))
                w2 = ((hi - lo) / 2) ** 2
                scale = 1 / w2
        elif "bound" in just:
            # a one-sided bound of a rescaled variable: x - lo (resp. hi - x) is implied by the
            # query's tightest bound (x - lo = (x - lo') + (lo' - lo) with lo' >= lo)
            v = just["bound"]; side = just["side"]
            if v not in cidx or v not in names: dropped.append(f"bound {v}: unknown variable"); continue
            i = names.index(v); mp = cert["map"][v]
            if "lo" not in mp: dropped.append(f"bound {v}: no box in the map"); continue
            lo, hi = Fraction(mp["lo"]), Fraction(mp["hi"]); w = (hi - lo) / 2
            if w == 0: dropped.append(f"bound {v}: point variable"); continue
            m1 = tuple(1 if j == i else 0 for j in range(nv))
            if side == "lo":
                if i not in lo_b or lo_b[i] < lo: dropped.append(f"bound {v} >= {lo} not implied by the query"); continue
                hpoly = sub({m1: Fraction(1), (0,) * nv: -lo})
            else:
                if i not in hi_b or hi_b[i] > hi: dropped.append(f"bound {v} <= {hi} not implied by the query"); continue
                hpoly = sub({m1: Fraction(-1), (0,) * nv: hi})
            scale = 1 / w
        elif "atom" in just:
            i = just["atom"]
            if not (0 <= i < len(hyps)) or hyps[i][0] == "eq": dropped.append(f"atom {i}: not an inequality atom"); continue
            hpoly = hy[i][1]; scale = Fraction(just.get("scale", 1))
            if scale <= 0: dropped.append(f"atom {i}: non-positive scale"); continue
        elif "prod" in just:
            i, j = just["prod"]
            if not (0 <= i < len(hyps) and 0 <= j < len(hyps)) or "eq" in (hyps[i][0], hyps[j][0]):
                dropped.append(f"prod {i},{j}: not inequality atoms"); continue
            hpoly = pmul(hy[i][1], hy[j][1]); scale = Fraction(just.get("scale", 1))
            if scale <= 0: dropped.append(f"prod {i},{j}: non-positive scale"); continue
        elif "poly" in just:
            # a polynomial in the original variables (the probe's format): it must be an inequality atom up to a positive factor
            try: p = sympy_poly_to_dict(just["poly"], names)
            except Exception as ex: dropped.append(f"mult {mi}: unparsable polynomial ({ex})"); continue
            r = match_atom(p, hyps)
            if r is None: dropped.append(f"mult {mi}: polynomial is not a hypothesis atom"); continue
            i, f = r
            hpoly = hy[i][1]; scale = f
        else:
            dropped.append(f"mult {mi}: no justification"); continue
        if len(mult["gram"]) != len(mult["basis"]) or any(len(r) != len(mult["basis"]) for r in mult["gram"]):
            return f"REJECTED multiplier {mi} Gram/basis size mismatch"
        basis, Gf = restrict(pad(mult["basis"]), mult["gram"])
        Gf, mineig, projected = project_psd(Gf)
        if projected: nproj += 1
        G = [[to_frac(x) for x in row] for row in Gf]
        n = len(basis)
        for a in range(n):
            for b in range(a + 1, n):
                G[a][b] = G[b][a] = (G[a][b] + G[b][a]) / 2
        ok, minp, why = ldl_psd(G)
        if not ok: return f"REJECTED multiplier {mi} Gram not PSD (min eigenvalue {mineig:.2e}): {why}"
        rhs = padd(rhs, pmul(pscale(gram_form(basis, G), scale), hpoly))
        nmult += 1
    neq = 0
    for ei, e in enumerate(cert.get("eq", [])):
        just = e["just"]
        if "atom" in just:
            j = just["atom"]
            if not (0 <= j < len(hyps)) or hyps[j][0] != "eq": dropped.append(f"eq {ei}: atom {j} is not an equality"); continue
            epoly = hy[j][1]; scale = Fraction(just.get("scale", 1))
        elif "poly" in just:
            try: p = sympy_poly_to_dict(just["poly"], names)
            except Exception as ex: dropped.append(f"eq {ei}: unparsable polynomial ({ex})"); continue
            r = None
            for j, (k, h) in enumerate(hyps):
                if k != "eq" or not h: continue
                m0 = next(iter(p)) if p else None
                if m0 is None or m0 not in h: continue
                f = p[m0] / h[m0]
                if pscale(h, f) == p: r = (j, f); break
            if r is None: dropped.append(f"eq {ei}: polynomial is not an equality atom"); continue
            j, scale = r; epoly = hy[j][1]
        else:
            dropped.append(f"eq {ei}: no justification"); continue
        if len(e["coeffs"]) != len(e["basis"]): return f"REJECTED equality multiplier {ei} size mismatch"
        basis = pad(e["basis"]); coeffs = [to_frac(x) for x in e["coeffs"]]
        q = {}
        for m, c in zip(basis, coeffs):
            if c and all(m[j] == 0 for j in point): q = padd(q, {m: c})
        rhs = padd(rhs, pmul(pscale(q, scale), epoly))
        neq += 1
    # residual, absorbed into s0
    resid = padd(target, pscale(rhs, -1))
    maxres = max((abs(c) for c in resid.values()), default=Fraction(0))
    pairs = {}
    for a in range(n0):
        for b in range(a, n0):
            m = tuple(x + y for x, y in zip(b0[a], b0[b]))
            if m not in pairs or (a == b and pairs[m][0] != pairs[m][1]): pairs[m] = (a, b)
    for m, c in resid.items():
        if m not in pairs:
            return f"REJECTED residual monomial {m} (coefficient {float(c):.3e}) outside the s0 basis products" + (f"; dropped: {dropped}" if dropped else "")
        a, b = pairs[m]
        if a == b: G0[a][a] += c
        else: G0[a][b] += c / 2; G0[b][a] += c / 2
    ok, minp, why = ldl_psd(G0)
    if not ok:
        return f"REJECTED s0 Gram not PSD after absorbing the residual (max |residual| {float(maxres):.2e}): {why}" + (f"; dropped: {dropped}" if dropped else "")
    return (f"VERIFIED cvars={len(cvars)} qvars={nv} hyps={len(hyps)} mult={nmult} eq={neq} basis0={n0} eps={eps} "
            f"maxres={float(maxres):.2e} minpivot={float(minp):.2e} projected={nproj} point={len(point)} dropped={len(dropped)} t={time.time() - t0:.1f}"
            + (f" dropped_reasons={dropped}" if dropped and verbose else ""))

def main(argv):
    verbose = "-v" in argv; argv = [a for a in argv if a != "-v"]
    try:
        if len(argv) == 3 and argv[1] == "--phase1":
            query, cert = load_phase1(argv[2])
        elif len(argv) == 3:
            query = open(argv[1]).read(); cert = load_json_cert(argv[2])
        else:
            sys.stderr.write(__doc__); return 2
        print(check(query, cert, verbose)); return 0
    except Exception as ex:
        print(f"REJECTED checker error: {type(ex).__name__}: {str(ex)[:200]}"); return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))

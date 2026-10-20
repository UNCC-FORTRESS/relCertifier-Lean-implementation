#!/usr/bin/env python3
"""Shared parsing for the non-vacuity and mutation checks (branch `mutation`).

Reads a `benchmarks/suite_v2/<name>/input.txt`, translates guards, evolve domains and
relational-invariant rows into SMT-LIB s-expressions with side-prefixed variables
(`L_x`, `R_x`), and writes invariant rows back as `smt2:` terms.
"""
import re
from fractions import Fraction

TOK = re.compile(r"\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_][A-Za-z0-9_]*)(\[[lr]\])?|(<=|>=|==|!=|<|>|=|\+|-|\*|/|\(|\)))")


def parse_sexpr(s):
    toks = re.findall(r"\(|\)|[^\s()]+", s)
    pos = 0
    def rd():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "(":
            lst = []
            while toks[pos] != ")":
                lst.append(rd())
            pos += 1
            return lst
        return t
    e = rd()
    assert pos == len(toks), s
    return e


def show(e):
    if isinstance(e, list):
        return "(" + " ".join(show(x) for x in e) + ")"
    return e


def num(q):
    q = Fraction(q)
    if q < 0:
        return ["-", num(-q)]
    if q.denominator == 1:
        return f"{q.numerator}.0"
    return ["/", f"{q.numerator}.0", f"{q.denominator}.0"]


class Infix:
    def __init__(self, s, side, svars):
        self.toks = []
        i = 0
        while i < len(s):
            m = TOK.match(s, i)
            if not m or m.end() == i:
                if s[i:].strip() == "":
                    break
                raise ValueError(f"cannot tokenize {s[i:]!r}")
            n, ident, br, op = m.groups()
            if n: self.toks.append(("num", n))
            elif ident:
                if ident in ("and",): self.toks.append(("and", ident))
                elif ident in ("or", "not"): raise ValueError("unsupported " + ident)
                elif br: self.toks.append(("var", ("L_" if br == "[l]" else "R_") + ident))
                else: self.toks.append(("var", (side + "_" + ident) if side else ident))
            else: self.toks.append(("op", op))
            i = m.end()
        self.p = 0
    def peek(self):
        return self.toks[self.p] if self.p < len(self.toks) else (None, None)
    def eat(self, v=None):
        t = self.toks[self.p]; self.p += 1
        if v is not None: assert t[1] == v, (t, v)
        return t
    def conj(self):
        atoms = [self.cmp()]
        while self.peek()[0] == "and":
            self.eat(); atoms.append(self.cmp())
        assert self.p == len(self.toks), self.toks[self.p:]
        return atoms
    def cmp(self):
        a = self.sum(); op = self.eat()[1]; b = self.sum()
        op = {"==": "=", "=": "="}.get(op, op)
        assert op in ("<=", ">=", "<", ">", "="), op
        return [op, a, b]
    def sum(self):
        e = self.term()
        while self.peek()[1] in ("+", "-"):
            o = self.eat()[1]; e = [o, e, self.term()]
        return e
    def term(self):
        e = self.fac()
        while self.peek()[1] in ("*", "/"):
            o = self.eat()[1]; e = [o, e, self.fac()]
        return e
    def fac(self):
        k, v = self.peek()
        if v == "-":
            self.eat(); return ["-", self.fac()]
        if v == "(":
            self.eat(); e = self.sum(); self.eat(")"); return e
        self.eat()
        if k == "num": return v if "." in v else v + ".0"
        return v


def rename(e, side, svars):
    if isinstance(e, list):
        return [rename(x, side, svars) for x in e]
    return side + "_" + e if e in svars else e


def atoms_of(expr, side, svars):
    """Formula text -> list of atom s-exprs (a conjunction)."""
    expr = expr.strip()
    if expr.startswith("smt2:"):
        e = parse_sexpr(expr[5:].strip())
        if side: e = rename(e, side, svars)
        if isinstance(e, list) and e[0] == "and":
            return e[1:]
        return [e]
    return Infix(expr, side, svars).conj()


def const_term(e):
    """Value of a polynomial s-expr with every variable at 0."""
    if isinstance(e, list):
        op, args = e[0], [const_term(x) for x in e[1:]]
        if op == "+": return sum(args, Fraction(0))
        if op == "-": return -args[0] if len(args) == 1 else args[0] - sum(args[1:], Fraction(0))
        if op == "*":
            r = Fraction(1)
            for a in args: r *= a
            return r
        if op == "/": return args[0] / args[1]
        raise ValueError(op)
    try:
        return Fraction(e)
    except ValueError:
        return Fraction(0)


def tighten(atom, frac):
    """Shrink the set of `a op b` by frac of its constant slack; None if no slack."""
    op, a, b = atom
    if op not in ("<=", "<", ">=", ">"):
        return None
    c = const_term(["-", b, a])
    d = abs(c) * Fraction(str(frac))
    if d == 0:
        return None
    if op in ("<=", "<"):
        return [op, a, ["-", b, num(d)]]
    return [op, a, ["+", b, num(d)]]


def parse_bench(text):
    """Sections -> dict; modes per side with guard/evolve; invariant rows in order."""
    sec = None
    out = {"L": {"vars": [], "modes": {}}, "R": {"vars": [], "modes": {}}, "rows": []}
    for ln, line in enumerate(text.split("\n")):
        s = line.split("#", 1)[0].rstrip() if not line.lstrip().startswith("#") else ""
        if not s.strip():
            continue
        m = re.match(r"^\[(.*)\]$", s.strip())
        if m:
            sec = m.group(1); continue
        if sec in ("Lsys", "Rsys") and s.startswith("state_vars"):
            out[sec[0]]["vars"] = [v.strip() for v in s.split("=", 1)[1].strip()[1:-1].split(",")]
        mm = re.match(r"^(Lsys|Rsys)\.mode\.(\w+)$", sec or "")
        if mm and "=" in s:
            k, v = s.split("=", 1)
            out[mm.group(1)[0]]["modes"].setdefault(mm.group(2), {})[k.strip()] = v.strip()
        if sec == "relational_invariant" and "=" in s:
            k, v = s.split("=", 1)
            out["rows"].append((ln, k.strip(), v.strip()))
    return out

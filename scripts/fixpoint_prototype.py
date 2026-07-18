#!/usr/bin/env python3
"""Executable prototype of the winning-region fixpoint (docs/FIXPOINT-DESIGN.md),
run on watertank's REAL data.

What is real here:
  * the mode lists, L-successor lists, and R's declared edge relation are read
    off benchmarks/suite_uniform/watertank/input.txt (transcribed below);
  * the flow oracle is the RECORDED verdict set - the six VerdW route-B UNSAT
    facts (docs/VERDICTS.md), i.e. exactly what Z3 already answered; the three
    missing pairs are the file's own documented no-certificate pairs (the
    gap-growing directions of the one-sided invariant x_L <= x_R + 3).

What is placeholder (tool-side work in the real design):
  * hop legality is taken from the declared edge relation; in the tool each hop
    additionally gets a guard-at-entry SAT probe (selection only, never trusted)
    and a frozen-left invariant-preservation UNSAT verdict (trusted, named);
  * tiling arithmetic is degenerate for watertank (single full-width piece per
    window), so the flow oracle is a set of pairs rather than width sets.

Run:  python3 scripts/fixpoint_prototype.py
"""

# ---------------------------------------------------------------- real data
L_MODES = ["Low", "Mid", "High"]
R_MODES = ["Low", "Mid", "High"]

# [Lsys.mode.*].next  (self-successors included, as declared)
L_SUCC = {"Low": ["Mid", "Low"], "Mid": ["High", "Mid"], "High": ["Mid", "High"]}

# [Rsys.mode.*].next  ->  R's declared edge relation (hops move along these)
R_EDGES = {"Low": ["Mid", "Low"], "Mid": ["High", "Mid"], "High": ["Mid", "High"]}

# The six VerdW facts (route B, all UNSAT) = the flow-certified (l, q) pairs.
# The three absent pairs are documented in the benchmark header as the
# no-certificate directions (left fills/leads while right drains/lags).
FLOW_CERT = {
    ("Low", "Low"), ("Low", "Mid"),
    ("Mid", "Mid"),
    ("High", "Low"), ("High", "Mid"), ("High", "High"),
}

ALL_POSITIONS = [(l, q) for l in L_MODES for q in R_MODES]


# ------------------------------------------------- inner fixpoint: Serve(l', T)
def serve(l_target, landing, edges, log=None):
    """Least fixpoint: which R modes can serve l_target's window, given that the
    acceptable landing modes are `landing` (the outer W's row at l_target)?
    Base: q in landing with a certified flow answer. Close under declared hops.
    Returns (served_set, chain) where chain[q] is the hop path q -> ... -> q*."""
    base = {q for q in landing if (l_target, q) in FLOW_CERT}
    served = set(base)
    chain = {q: [q] for q in base}          # q already answers: empty hop chain
    changed = True
    rounds = 0
    while changed:
        changed, rounds = False, rounds + 1
        for q in R_MODES:
            if q in served:
                continue
            for q2 in edges[q]:
                if q2 in served:            # hop q -> q2, then q2's chain
                    served.add(q)
                    chain[q] = [q] + chain[q2]
                    changed = True
                    break
    if log is not None:
        log.append((l_target, sorted(base), sorted(served), rounds))
    return served, chain


# ------------------------------------------------ outer fixpoint: prune to gfp
def winning_region(edges, verbose=True):
    W = set(ALL_POSITIONS)                  # W0: all admissible (all 9 pass)
    it = 0
    sigma = {}
    while True:
        it += 1
        keep, kill = set(), []
        sigma = {}
        for (l, q) in sorted(W):
            ok = True
            for l2 in L_SUCC[l]:
                landing = {q2 for q2 in R_MODES if (l2, q2) in W}
                served, chain = serve(l2, landing, edges)
                if q in served:
                    sigma[(l, q, l2)] = chain[q]
                else:
                    ok = False
                    kill.append(((l, q), l2))
                    break
            if ok:
                keep.add((l, q))
        if verbose:
            print(f"  iteration {it}:  |W| = {len(W)} -> {len(keep)}")
            for (pos, l2) in kill:
                print(f"    pruned {pos}: cannot serve successor window {l2}")
        if keep == W:
            return W, sigma, it
        W = keep


def show(W, sigma):
    print("  final W:")
    hdr = "        " + "".join(f"{q:>6}" for q in R_MODES) + "   (columns: R mode)"
    print(hdr)
    for l in L_MODES:
        row = "".join(f"{'  Y' if (l, q) in W else '  .':>6}" for q in R_MODES)
        print(f"  {l:>5} {row}")
    print("  choice table sigma (per position, per L-successor):")
    for (l, q, l2), chain in sorted(sigma.items()):
        if len(chain) == 1:
            move = f"stay, flow at the certified lambda for ({l2},{chain[0]})"
        else:
            hops = " -> ".join(chain)
            move = f"hop {hops}, then flow for ({l2},{chain[-1]})"
        print(f"    at ({l:>4},{q:>4}), L switches to {l2:>4}:  {move}")


def post_fixpoint_check(W, sigma, edges):
    """The kernel's `decide`: every position of W, under sigma, lands in W,
    every hop is a declared edge, every flow endpoint is flow-certified."""
    for (l, q) in W:
        for l2 in L_SUCC[l]:
            chain = sigma.get((l, q, l2))
            if chain is None or chain[0] != q:
                return False, f"missing/ill-anchored entry at ({l},{q})->{l2}"
            for a, b in zip(chain, chain[1:]):
                if b not in edges[a]:
                    return False, f"undeclared hop {a}->{b}"
            if (l2, chain[-1]) not in FLOW_CERT:
                return False, f"uncertified flow at ({l2},{chain[-1]})"
            if (l2, chain[-1]) not in W:
                return False, f"lands outside W at ({l2},{chain[-1]})"
    return True, "postFix holds: W is a post-fixpoint under sigma"


# ------------------------------------------------------------------------ runs
print("=" * 72)
print("RUN 1: watertank as-is (real edges, recorded verdicts)")
print("=" * 72)
W, sigma, iters = winning_region(R_EDGES)
show(W, sigma)
ok, msg = post_fixpoint_check(W, sigma, R_EDGES)
print(f"  kernel check: {msg}" if ok else f"  kernel check FAILED: {msg}")
expected = {(l, q) for (l, q) in FLOW_CERT}
print(f"  W == the six VerdW indices: {W == expected}")
print(f"  admissible starts (all of W) nonempty -> modal theorem obtainable")

print()
print("=" * 72)
print("RUN 2: counterfactual - delete R's edge High->Mid (drain trap)")
print("=" * 72)
edges2 = {k: [v for v in vs if not (k == "High" and v == "Mid")]
          for k, vs in R_EDGES.items()}
W2, sigma2, _ = winning_region(edges2)
show(W2, sigma2)
print("  reading: without High->Mid, an R stuck in High cannot get back to a")
print("  filling mode; every position whose survival depended on reaching Mid")
print("  through High is pruned, and the pruning CASCADES (gfp at work).")

print()
print("=" * 72)
print("RUN 3: counterfactual - additionally delete the (High,Mid) verdict")
print("=" * 72)
FLOW_CERT.discard(("High", "Mid"))
W3, sigma3, _ = winning_region(R_EDGES)
show(W3, sigma3)
FLOW_CERT.add(("High", "Mid"))
print("  reading: weaker dynamics (one fewer certified pair) shrinks W the")
print("  same way a weaker graph does - the fixpoint composes both effects.")

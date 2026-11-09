"""Independent re-implementation (shrink-review-r1) of the shrinking operation (15)-(16) and the
Appendix A.1 strategies of Kobeaga-Merino-Lozano, arXiv:2004.14574v4.  Written from the source
text only; the r123 lane's scripts were NOT read or imported.

State: a partition of the original vertex set into blocks (current vertices).  By (16b)/(16a) the
edge value between two blocks is the sum of the original edge values between them; by (16c) an
unmerged vertex keeps its y; by (16d) a merged vertex gets half of its boundary value (which, by
(16b) applied repeatedly, is the original boundary value of the union).  The support graph has an
edge between two blocks iff their edge value is > 0 (15b restricted to the support graph).

Semantics enumerated:
  * HEAP-P : literal pseudocode; after a shrink H <- H[S] (eq. (17): s enters H iff S meets H)
             then H <- H u N(s)  (SHRINK/UPDATE lines 4 and 21).
  * HEAP-T : Section 6.2 prose: remove S from H, then add s and its neighbours.
  * RULE   : any applicable pair may be shrunk at any time; terminal = no applicable pair.
In the heap semantics the choice of u in H ("Select a vertex u in H") and the scan order of N(u)
are free; the first applicable neighbour in the scan is shrunk and the scan stops (goto).
Every reachable terminal state (H empty) is collected.
"""
import itertools, json, sys
from fractions import Fraction as F
from functools import lru_cache

HALF = F(1, 2)
N = 6
Y0 = (HALF, F(1), F(1), F(1), F(1), F(1))
EDGES = {(0, 4): HALF, (0, 5): HALF, (2, 3): HALF, (2, 5): HALF, (3, 4): HALF,
         (1, 2): F(1), (1, 3): F(1), (4, 5): F(1)}


def mk_x(n, edges):
    x = [[F(0)] * n for _ in range(n)]
    for (a, b), v in edges.items():
        x[a][b] = x[b][a] = v
    return tuple(tuple(r) for r in x)


def in_PA(n, y, x):
    """(7a),(7b),(7e),(7f) on K_n; returns list of failures."""
    bad = []
    for v in range(n):
        if sum(x[v]) != 2 * y[v]:
            bad.append(("7a", v))
        if not (0 <= y[v] <= 1):
            bad.append(("7e", v))
        for w in range(n):
            if w != v:
                if x[v][w] > y[v]:
                    bad.append(("7b", v, w))
                if x[v][w] < 0:
                    bad.append(("7f", v, w))
                if x[v][w] != x[w][v]:
                    bad.append(("sym", v, w))
    return bad


class Inst:
    def __init__(self, n, y, x):
        self.n, self.y, self.x = n, y, x

    def X(self, A, B):
        return sum((self.x[a][b] for a in A for b in B), F(0))

    def Y(self, A):
        if len(A) == 1:
            (a,) = tuple(A)
            return self.y[a]                                   # (16c)
        rest = [v for v in range(self.n) if v not in A]
        return self.X(A, rest) / 2                             # (16d)

    def nbrs(self, P, A):
        return [B for B in P if B != A and self.X(A, B) > 0]   # support graph, (15b)

    # ---- rule tests -------------------------------------------------------------------------
    def s1(self, P, u, v):
        c = self.Y(u)
        if self.Y(v) == c and self.X(u, v) == c:
            return any(self.Y(w) >= c for w in P if w != u and w != v)   # Theorem 4.4 witness
        return False

    def s1s2_branch(self, P, u, v):
        """Algorithm S1S2 lines 6-16 for the scanned pair (u, v): returns rule name or None."""
        c = self.Y(u)
        xv = self.X(u, v)
        if self.Y(v) == c and xv == c:
            if any(self.Y(w) >= c for w in P if w != u and w != v):
                return "S1"
            return None                         # no fall-through to the else-if
        elif xv > self.Y(u) and xv > self.Y(v):
            return "S2"
        return None

    def c1_branch(self, P, u, v, mode):
        """Algorithms C1 / C1C2 / C1C2C3 for scanned pair (u, v). Returns (rule, S) or None."""
        c = self.Y(u)
        if not (self.Y(v) == c and self.X(u, v) == c):
            return None
        for t in self.nbrs(P, v):
            if t == u:
                continue
            if mode == "C1":
                if self.Y(t) == c and self.X(v, t) == c:
                    return ("C1", frozenset([u, v]))
            else:
                if self.Y(t) == c and self.X(u, t) + self.X(v, t) == c:
                    return ("C2", frozenset([u, v]))
        if mode == "C1C2C3":
            # Theorem 3.6 with |S| = 3 (the printed pseudocode has an unbound t on line 15 and
            # omits y_w = c and x[w,t]; we use the theorem's hypotheses (i)-(iii)).
            for w in self.nbrs(P, v):
                if w == u or self.Y(w) != c:
                    continue
                S = [u, v, w]
                if self.X(u, v) + self.X(u, w) + self.X(v, w) != 2 * c:
                    continue
                for t in P:
                    if t in S:
                        continue
                    if self.Y(t) == c and sum((self.X(t, z) for z in S), F(0)) == c:
                        return ("C3", frozenset(S))
        return None

    def rule_moves(self, P, strat):
        """Rule-level moves: all (rule, S) applicable anywhere."""
        out = set()
        for u in P:
            for v in self.nbrs(P, u):
                if strat == "S1S2":
                    r = self.s1s2_branch(P, u, v)
                    if r:
                        out.add((r, frozenset([u, v])))
                elif strat == "S1":
                    if self.s1(P, u, v):
                        out.add(("S1", frozenset([u, v])))
                else:
                    # enumerate every C-move with u as the scanned vertex (all t / w choices)
                    out |= self.all_c_moves(P, u, v, strat)
        return out

    def all_c_moves(self, P, u, v, mode):
        c = self.Y(u)
        res = set()
        if not (self.Y(v) == c and self.X(u, v) == c):
            return res
        for t in self.nbrs(P, v):
            if t == u:
                continue
            if mode == "C1" and self.Y(t) == c and self.X(v, t) == c:
                res.add(("C1", frozenset([u, v])))
            if mode != "C1" and self.Y(t) == c and self.X(u, t) + self.X(v, t) == c:
                res.add(("C2", frozenset([u, v])))
        if mode == "C1C2C3":
            for w in self.nbrs(P, v):
                if w == u or self.Y(w) != c:
                    continue
                S = [u, v, w]
                if self.X(u, v) + self.X(u, w) + self.X(v, w) != 2 * c:
                    continue
                for t in P:
                    if t not in S and self.Y(t) == c and sum((self.X(t, z) for z in S), F(0)) == c:
                        res.add(("C3", frozenset(S)))
        return res

    def scan_moves(self, P, u, strat):
        """Possible first-applicable outcomes when u is popped, over all scan orders of N(u)."""
        res = set()
        for v in self.nbrs(P, u):
            if strat == "S1S2":
                r = self.s1s2_branch(P, u, v)
                if r:
                    res.add((r, frozenset([u, v])))
            elif strat == "S1":
                if self.s1(P, u, v):
                    res.add(("S1", frozenset([u, v])))
            else:
                # with a free scan order of N(v) / N(w) too, any applicable (t, w) can come first
                res |= self.all_c_moves(P, u, v, strat)
        return res


def shrink(P, S):
    s = frozenset().union(*S)
    return frozenset([B for B in P if B not in S] + [s]), s


def heap_update(inst, P2, s, H, S, variant):
    if variant == "P":                                        # literal: H <- H[S]
        H2 = set(B for B in H if B not in S)
        if any(B in H for B in S):
            H2.add(s)
    else:                                                     # prose: always add s
        H2 = set(B for B in H if B not in S) | {s}
    H2 |= set(inst.nbrs(P2, s))                               # SHRINK/UPDATE line 21
    return frozenset(H2)


def explore_heap(inst, strat, variant):
    P0 = frozenset(frozenset([v]) for v in range(inst.n))
    start = (P0, P0)
    seen, stack, terminals, nstates = {start}, [start], set(), 0
    while stack:
        P, H = stack.pop()
        nstates += 1
        if not H:
            terminals.add(P)
            continue
        for u in H:
            Hm = H - {u}
            mv = inst.scan_moves(P, u, strat)
            succ = []
            if not mv:
                succ.append((P, Hm))
            for (_, S) in mv:
                P2, s = shrink(P, S)
                succ.append((P2, heap_update(inst, P2, s, Hm, S, variant)))
            for st in succ:
                if st not in seen:
                    seen.add(st)
                    stack.append(st)
    return terminals, nstates


def explore_rule(inst, strat):
    P0 = frozenset(frozenset([v]) for v in range(inst.n))
    seen, stack, terminals, edges = {P0}, [P0], set(), 0
    while stack:
        P = stack.pop()
        mv = inst.rule_moves(P, strat)
        if not mv:
            terminals.add(P)
        for (_, S) in mv:
            edges += 1
            P2, _ = shrink(P, S)
            if P2 not in seen:
                seen.add(P2)
                stack.append(P2)
    return terminals, len(seen)


def describe(inst, P):
    blocks = sorted(P, key=lambda B: (len(B), sorted(B)))
    ys = {tuple(sorted(B)): str(inst.Y(B)) for B in blocks}
    es = {}
    for A, B in itertools.combinations(blocks, 2):
        v = inst.X(A, B)
        if v > 0:
            es["%s-%s" % (sorted(A), sorted(B))] = str(v)
    return {"nverts": len(blocks), "nedges": len(es), "blocks": [sorted(B) for B in blocks],
            "y": {str(k): v for k, v in ys.items()}, "x": es}


def weighted_canon(inst, P):
    """Canonical form of the weighted, y-labelled support graph (brute force; <= 6 vertices)."""
    blocks = list(P)
    best = None
    for perm in itertools.permutations(range(len(blocks))):
        bl = [blocks[i] for i in perm]
        key = (tuple(inst.Y(B) for B in bl),
               tuple(inst.X(bl[i], bl[j]) for i in range(len(bl)) for j in range(i + 1, len(bl))))
        if best is None or key < best:
            best = key
    return best


def plain_canon(inst, P):
    blocks = list(P)
    best = None
    for perm in itertools.permutations(range(len(blocks))):
        bl = [blocks[i] for i in perm]
        key = tuple(inst.X(bl[i], bl[j]) > 0 for i in range(len(bl)) for j in range(i + 1, len(bl)))
        if best is None or key < best:
            best = key
    return (len(blocks), best)


def check_run(inst, steps, strat="S1S2"):
    """Replay an explicit rule-level sequence; each step must be applicable."""
    P = frozenset(frozenset([v]) for v in range(inst.n))
    log = []
    for S in steps:
        S = frozenset(frozenset(b) if isinstance(b, (set, frozenset, tuple, list)) else frozenset([b]) for b in S)
        mv = {m[1]: m[0] for m in inst.rule_moves(P, strat)}
        assert S in mv, ("not applicable", [sorted(b) for b in S])
        P, s = shrink(P, S)
        log.append({"rule": mv[S], "merged": sorted(s), "y_new": str(inst.Y(s))})
    final_moves = inst.rule_moves(P, strat)
    return P, log, sorted([(r, sorted(sorted(b) for b in S)) for r, S in final_moves])


def deterministic_run(inst, order_key, policy, variant="P"):
    """A fixed implementation: H kept as an ordered container; policy FIFO / LIFO / MIN.
    order_key: rank of original vertices; a block's rank is min rank of its members.
    Neighbours scanned by increasing rank."""
    P = frozenset(frozenset([v]) for v in range(inst.n))
    rank = lambda B: min(order_key[v] for v in B)
    H = sorted(P, key=rank)
    while H:
        if policy == "FIFO":
            u = H.pop(0)
        elif policy == "LIFO":
            u = H.pop()
        else:
            u = min(H, key=rank); H.remove(u)
        hit = None
        for v in sorted(inst.nbrs(P, u), key=rank):
            if inst.s1s2_branch(P, u, v):
                hit = frozenset([u, v]); break
        if hit is None:
            continue
        P, s = shrink(P, hit)
        inH = any(B in H for B in hit)
        H = [B for B in H if B not in hit]
        if variant == "T" or inH:
            H.append(s)
        for nb in sorted(inst.nbrs(P, s), key=rank):
            if nb not in H:
                H.append(nb)
    return len(P)


def main():
    out = {}
    x = mk_x(N, EDGES)
    inst = Inst(N, Y0, x)
    out["in_PA_failures"] = in_PA(N, Y0, x)
    # explicit runs
    PA, logA, finA = check_run(inst, [[4, 5], [1, 2], [(1, 2), 3]])
    PB, logB, finB = check_run(inst, [[1, 2], [(1, 2), 3]])
    out["runA"] = {"steps": logA, "final": describe(inst, PA), "moves_left": finA}
    out["runB"] = {"steps": logB, "final": describe(inst, PB), "moves_left": finB}
    # exhaustive enumeration
    res = {}
    for strat in ["S1S2", "S1", "C1", "C1C2", "C1C2C3"]:
        r = {}
        for sem in ["HEAP-P", "HEAP-T", "RULE"]:
            if sem == "RULE":
                T, ns = explore_rule(inst, strat)
            else:
                T, ns = explore_heap(inst, strat, sem[-1])
            r[sem] = {"states": ns, "n_terminal_partitions": len(T),
                      "terminal_vertex_counts": sorted(set(len(P) for P in T)),
                      "n_weighted_iso_classes": len(set(weighted_canon(inst, P) for P in T)),
                      "n_plain_iso_classes": len(set(plain_canon(inst, P) for P in T)),
                      "terminals": sorted([describe(inst, P) for P in T],
                                          key=lambda d: (d["nverts"], str(d["blocks"])))}
        res[strat] = r
    out["enumeration"] = res
    # fixed deterministic implementations over all 720 relabellings
    det = {}
    for policy in ["FIFO", "LIFO", "MIN"]:
        for variant in ["P", "T"]:
            for presort in ["index", "y-desc-then-index"]:
                cnt = {}
                for perm in itertools.permutations(range(N)):
                    key = list(perm)
                    if presort == "y-desc-then-index":
                        # EH line 1: V sorted decreasingly by y; ties by the relabelled index
                        order = sorted(range(N), key=lambda v: (-Y0[v], perm[v]))
                        key = [0] * N
                        for i, v in enumerate(order):
                            key[v] = i
                    k = deterministic_run(inst, key, policy, variant)
                    cnt[k] = cnt.get(k, 0) + 1
                det["%s/%s/%s" % (policy, variant, presort)] = {str(k): v for k, v in sorted(cnt.items())}
    out["deterministic_over_720_labellings"] = det
    json.dump(out, sys.stdout, indent=1, default=str)


if __name__ == "__main__":
    main()

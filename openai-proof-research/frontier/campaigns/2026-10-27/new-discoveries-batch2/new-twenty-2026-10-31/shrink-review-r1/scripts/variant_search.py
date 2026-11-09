"""shrink-review-r1: exhaustive half-integral search for non-confluence of S1S2 under semantic
variants (own code; r123 scripts not used).

Points: n vertices, y_v in {1/2, 1}, x_e in {0, 1/2, 1}, (7a),(7b) (hence (7e),(7f)) on K_n.
Scaled units: Y = 2y in {1,2}, X = 2x in {0,1,2}.  For a block B the value is
y(B) = x(delta(B))/2, i.e. 2*Y(B) = boundary_X(B) for merged blocks (16d); singletons keep Y.
We compare doubled quantities to stay in integers: YY(B) = 2*Y(B), XX = 2*X.

Variants (rule level; see REVIEW.md for the heap/rule equivalence argument):
  V1  paper  : S1 needs x=y_u=y_v=c and a witness w (y_w >= c);  S2: x > max(y_u, y_v).
  V2  code   : S1 without the witness (authors' cpsrksec s1.c); S2 only when > 2 vertices
               (s1.c: graph->n3v > 2).
  V3  depot  : V1 with a designated vertex d (y_d = 1, chosen as the last value-1 vertex) that is
               never shrunk (D treated as fixed); the witness then always exists for c <= 1.
usage: variant_search.py n k_lo k_hi   (k = number of value-1/2 vertices, placed first)
"""
import sys, itertools, json


def gen_points(n, k):
    Y = [1] * k + [2] * (n - k)
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    X = {}
    res = [2 * Y[v] for v in range(n)]          # remaining degree, scaled: sum X = 2Y
    # last edge index touching each vertex, for pruning
    last = [max(idx for idx, e in enumerate(edges) if v in e) for v in range(n)]

    def rec(idx):
        if idx == len(edges):
            if all(r == 0 for r in res):
                yield dict(X)
            return
        i, j = edges[idx]
        m = min(Y[i], Y[j], res[i], res[j])
        for val in range(m, -1, -1):
            res[i] -= val; res[j] -= val
            ok = True
            for v in (i, j):
                if last[v] == idx and res[v] != 0:
                    ok = False
            if ok:
                X[(i, j)] = val
                yield from rec(idx + 1)
            res[i] += val; res[j] += val
        X.pop((i, j), None)
    for pt in rec(0):
        yield Y, pt


class St:
    def __init__(self, n, Y, Xd):
        self.n = n
        self.Y = Y
        self.x = [[0] * n for _ in range(n)]
        for (i, j), v in Xd.items():
            self.x[i][j] = self.x[j][i] = v

    def XX(self, A, B):   # doubled scaled edge value between blocks (bitmasks)
        s = 0
        for a in range(self.n):
            if A >> a & 1:
                row = self.x[a]
                for b in range(self.n):
                    if B >> b & 1:
                        s += row[b]
        return 2 * s

    def YY(self, A):      # doubled scaled vertex value
        if A & (A - 1) == 0:
            return 2 * self.Y[A.bit_length() - 1]
        full = (1 << self.n) - 1
        return self.XX(A, full & ~A) // 2 * 1 if False else self._bd(A)

    def _bd(self, A):
        full = (1 << self.n) - 1
        return self.XX(A, full & ~A) // 2   # 2*Y(B) = boundary_X ; XX = 2*boundary_X -> /2

    def moves(self, P, variant, depot):
        out = []
        ys = {B: self.YY(B) for B in P}
        Pl = list(P)
        for a in range(len(Pl)):
            for b in range(a + 1, len(Pl)):
                u, v = Pl[a], Pl[b]
                if variant == "V3" and ((u >> depot & 1) or (v >> depot & 1)):
                    continue
                xv = self.XX(u, v)
                if xv <= 0:
                    continue
                yu, yv = ys[u], ys[v]
                if yu == yv and xv == yu:
                    if variant == "V2":
                        out.append(u | v)
                    else:
                        if any(ys[w] >= yu for w in Pl if w != u and w != v):
                            out.append(u | v)
                elif xv > yu and xv > yv:
                    if variant == "V2" and len(Pl) <= 2:
                        continue
                    out.append(u | v)
        return out

    def explore(self, variant, depot):
        P0 = frozenset(1 << v for v in range(self.n))
        seen, stack, term = {P0}, [P0], set()
        while stack:
            P = stack.pop()
            mv = self.moves(P, variant, depot)
            if not mv:
                term.add(P)
            for S in mv:
                P2 = frozenset([B for B in P if B & S == 0] + [S])
                if P2 not in seen:
                    seen.add(P2); stack.append(P2)
        return term

    def inv(self, P):
        Pl = list(P)
        ys = sorted(self.YY(B) for B in Pl)
        xs = sorted(self.XX(Pl[i], Pl[j]) for i in range(len(Pl)) for j in range(i + 1, len(Pl))
                    if self.XX(Pl[i], Pl[j]) > 0)
        return (len(Pl), len(xs), tuple(ys), tuple(xs))

    def canon(self, P):
        Pl = list(P)
        best = None
        for perm in itertools.permutations(Pl):
            key = (tuple(self.YY(B) for B in perm),
                   tuple(self.XX(perm[i], perm[j]) for i in range(len(perm)) for j in range(i + 1, len(perm))))
            if best is None or key < best:
                best = key
        return best


def main():
    n, klo, khi = map(int, sys.argv[1:4])
    variants = sys.argv[4].split(",") if len(sys.argv) > 4 else ["V1", "V2", "V3"]
    stats = {}
    for k in range(klo, khi + 1):
        for Y, Xd in gen_points(n, k):
            st = St(n, Y, Xd)
            for var in variants:
                if var == "V3":
                    ones = [v for v in range(n) if Y[v] == 2]
                    if not ones:
                        continue
                    depots = ones          # try every value-1 vertex as the fixed depot
                    if len(sys.argv) > 5 and sys.argv[5] == "lastdepot":
                        depots = ones[-1:]  # WLOG: the labelled class is closed under permuting value-1 vertices
                else:
                    depots = [None]
                for d in depots:
                    T = st.explore(var, d)
                    key = "%s" % var
                    s = stats.setdefault(key, {"inputs": 0, "nonconfluent": 0, "examples": []})
                    s["inputs"] += 1
                    if len(T) > 1:
                        invs = set(st.inv(P) for P in T)
                        bad = len(invs) > 1 or len(set(st.canon(P) for P in T)) > 1
                        if bad:
                            s["nonconfluent"] += 1
                            if len(s["examples"]) < 3:
                                s["examples"].append({"n": n, "Y2": Y, "X2": {"%d-%d" % e: v for e, v in Xd.items() if v},
                                                      "depot": d, "terminal_vertex_counts": sorted(set(len(P) for P in T)),
                                                      "terminals": [sorted(sorted(b for b in range(n) if B >> b & 1) for B in P) for P in T]})
    print(json.dumps({"n": n, "k": [klo, khi], "variants": variants, "stats": stats}, indent=1))


if __name__ == "__main__":
    main()

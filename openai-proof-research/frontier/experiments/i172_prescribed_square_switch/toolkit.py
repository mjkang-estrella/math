"""Independent I172 finite graph / rational linear algebra implementation."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import gcd, lcm


def edge(a, b):
    return min(a, b), max(a, b)


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def add(*rows):
    return tuple(map(sum, zip(*rows)))


def scale(k, row):
    return tuple(k*x for x in row)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def differences(rows):
    rows = list(rows)
    return [sub(v, rows[0]) for v in rows[1:]]


def primitive(v):
    den = lcm(*(x.denominator if isinstance(x, Q) else 1 for x in v))
    v = [int(x*den) for x in v]
    d = gcd(*v)
    return tuple(x//d for x in v) if d else tuple(v)


def int_basis(rows):
    pivots = {}
    for row in rows:
        v = primitive(row)
        for p, b in sorted(pivots.items()):
            if v[p]:
                v = primitive(tuple(b[p]*x-v[p]*y for x, y in zip(v, b)))
        if any(v):
            p = next(i for i, x in enumerate(v) if x)
            pivots[p] = v
    return [pivots[k] for k in sorted(pivots)]


def fraction_rank(rows):
    # Independent reverse-column elimination, sparse rational dictionaries.
    basis = {}
    for row in rows:
        v = {i: Q(x) for i, x in enumerate(row) if x}
        while v:
            p = max(v)
            a = v[p]
            if p not in basis:
                basis[p] = {i: x/a for i, x in v.items()}
                break
            for i, x in basis[p].items():
                y = v.get(i, 0)-a*x
                if y:
                    v[i] = y
                else:
                    v.pop(i, None)
    return len(basis)


@lru_cache(maxsize=24000)
def _rank(rows):
    a, b = len(int_basis(rows)), fraction_rank(rows)
    assert a == b, (a, b)
    return a


def rank(rows):
    return _rank(tuple(sorted(set(tuple(r) for r in rows if any(r)))))


def quotient(row, basis):
    v = tuple(map(Q, row))
    for b in basis:
        p = next(i for i, x in enumerate(b) if x)
        if v[p]:
            v = sub(v, scale(v[p]/b[p], b))
    return v


def solve(rows, rhs, width):
    a = [list(map(Q, r))+[Q(y)] for r, y in zip(rows, rhs)]
    pivots, k = [], 0
    for j in range(width):
        i = next((i for i in range(k, len(a)) if a[i][j]), None)
        if i is None:
            continue
        a[k], a[i] = a[i], a[k]
        z = a[k][j]
        a[k] = [x/z for x in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                z = a[i][j]
                a[i] = [x-z*y for x, y in zip(a[i], a[k])]
        pivots.append(j)
        k += 1
    assert all(any(r[:-1]) or not r[-1] for r in a), "inconsistent"
    result = [Q(0)]*width
    for i, j in enumerate(pivots):
        result[j] = a[i][-1]
    assert all(dot(r, result) == y for r, y in zip(rows, rhs))
    return tuple(result)


class Graph:
    def __init__(self, record):
        self.record = record
        self.edges = tuple(sorted(edge(*e) for e in record["edges"]))
        self.vertices = tuple(sorted({v for e in self.edges for v in e}))
        self.n, self.m = len(self.vertices), len(self.edges)
        self.pos = {v: i for i, v in enumerate(self.vertices)}
        self.eid = {e: i for i, e in enumerate(self.edges)}
        self.adj = {v: [] for v in self.vertices}
        for i, (a, b) in enumerate(self.edges):
            self.adj[a].append((b, i))
            self.adj[b].append((a, i))

    def vector(self, edges):
        out = [0]*self.m
        for e in edges:
            out[self.eid[edge(*e)]] = 1
        return tuple(out)

    def unit(self, a, b):
        return self.vector([(a, b)])

    def components(self, row):
        todo = set(self.vertices)
        out = []
        while todo:
            stack = [min(todo)]
            seen = set(stack)
            while stack:
                v = stack.pop()
                for w, i in self.adj[v]:
                    if row[i] and w not in seen:
                        seen.add(w)
                        stack.append(w)
            todo -= seen
            out.append(tuple(sorted(seen)))
        return tuple(out)

    def validate(self):
        assert len(set(self.edges)) == self.m and all(a != b for a, b in self.edges)
        assert self.n == self.record["n"]
        assert all(len(self.adj[v]) == 3 for v in self.vertices)
        color = {self.vertices[0]: 0}
        stack = list(color)
        while stack:
            v = stack.pop()
            for w, _ in self.adj[v]:
                if w not in color:
                    color[w] = 1-color[v]
                    stack.append(w)
                assert color[w] != color[v]
        assert len(color) == self.n
        for removed in combinations(self.vertices, 2):
            avail = set(self.vertices)-set(removed)
            seen = {min(avail)}
            stack = list(seen)
            while stack:
                for w, _ in self.adj[stack.pop()]:
                    if w in avail and w not in seen:
                        seen.add(w)
                        stack.append(w)
            assert seen == avail
        darts = []
        links = {v: {} for v in self.vertices}
        for f in self.record["faces"]:
            assert len(f) == len(set(f))
            for j, v in enumerate(f):
                a, b = f[j-1], f[(j+1) % len(f)]
                assert edge(v, b) in self.eid
                darts.append((v, b))
                assert a not in links[v]
                links[v][a] = b
        assert Counter(darts) == Counter((a, b) for e in self.edges for a, b in (e, e[::-1]))
        for v, link in links.items():
            assert len(link) == 3
            start = next(iter(link))
            assert link[link[link[start]]] == start and link[start] != start
        assert self.n-self.m+len(self.record["faces"]) == 2
        return True

    def degree_sets(self, degrees, forbidden=()):
        # Vertex-saturation recursion: every undecided incident edge is fixed
        # at the chosen vertex. Branches partition all prescribed-degree sets.
        ban = set(forbidden)
        unknown = frozenset(i for i in range(self.m) if i not in ban)
        need = dict(degrees)
        result = []

        def visit(left, req, selected):
            if not left:
                if not any(req.values()):
                    result.append(tuple(int(i in selected) for i in range(self.m)))
                return
            best = None
            for v in self.vertices:
                incident = [i for _, i in self.adj[v] if i in left]
                q = req[v]
                if q < 0 or q > len(incident):
                    return
                if incident:
                    score = (0 if q in (0, len(incident)) else 1, len(incident), v)
                    if best is None or score < best[0]:
                        best = score, v, incident
            _, v, incident = best
            for chosen in combinations(incident, req[v]):
                r = req.copy()
                for i in chosen:
                    for w in self.edges[i]:
                        r[w] -= 1
                visit(left-set(incident), r, selected | set(chosen))

        visit(unknown, need, set())
        return tuple(sorted(result))

    def dfs_paths(self, start, end=None, forbidden=()):
        ban = set(forbidden)
        allmask = (1 << self.n)-1
        rows = set()

        def walk(v, seen, selected):
            if seen == allmask:
                if end is None:
                    close = self.eid.get(edge(v, start))
                    if close is None or close in ban:
                        return
                    selected = selected | {close}
                elif v != end:
                    return
                rows.add(tuple(int(i in selected) for i in range(self.m)))
                return
            if end is not None and v == end:
                return
            for w, i in self.adj[v]:
                bit = 1 << self.pos[w]
                if i not in ban and not seen & bit:
                    walk(w, seen | bit, selected | {i})

        walk(start, 1 << self.pos[start], set())
        return tuple(sorted(rows))

    def matchings(self):
        out = []

        def rec(available, chosen):
            if not available:
                out.append(tuple(int(i in chosen) for i in range(self.m)))
                return
            v = min(available)
            for w, i in self.adj[v]:
                if w in available:
                    rec(available-{v, w}, chosen | {i})

        rec(set(self.vertices), set())
        return tuple(sorted(out))

    def cycles(self):
        if not hasattr(self, "_cycles"):
            factors = self.degree_sets({v: 2 for v in self.vertices})
            cycles = tuple(r for r in factors if len(self.components(r)) == 1)
            assert cycles == self.dfs_paths(self.vertices[0])
            matching_complements = tuple(sorted(sub((1,)*self.m, r) for r in self.matchings()))
            assert factors == matching_complements
            self.factors, self._cycles = factors, cycles
        return self._cycles

    def families(self, step):
        fi, i, j = step
        f = self.record["faces"][fi]
        assert i < j and j-i >= 2 and len(f)-(j-i) >= 2 and (j-i) % 2 == 0
        u, v, y, x = f[i], f[(i+1) % len(f)], f[j], f[(j+1) % len(f)]
        e, h = self.eid[edge(u, v)], self.eid[edge(x, y)]
        cycles = self.cycles()
        fam = {f"N{a}{b}": tuple(c for c in cycles if (c[e], c[h]) == (a, b))
               for a in (0, 1) for b in (0, 1)}
        for key, endpoints in (("Pux", (u, x)), ("Pvy", (v, y)),
                               ("D11", (u, v, x, y))):
            rows = self.degree_sets({z: 1 if z in endpoints else 2 for z in self.vertices}, (e, h))
            if key == "D11":
                rows = tuple(r for r in rows if len(cs := self.components(r)) == 2
                             and any(u in s and v in s for s in cs)
                             and any(x in s and y in s for s in cs))
            else:
                rows = tuple(r for r in rows if len(self.components(r)) == 1)
                assert rows == self.dfs_paths(*endpoints, forbidden=(e, h))
            assert rows, (key, step)
            fam[key] = rows
        return fam, (u, v, x, y), (e, h)


def steps(record, face_length=None, minimal=False):
    for k, f in enumerate(record["faces"]):
        if face_length is not None and len(f) != face_length:
            continue
        for i in range(len(f)):
            for j in range(i+2, len(f)):
                if (j-i) % 2 or len(f)-(j-i) < 2:
                    continue
                if minimal and not (len(f) == 8 and j-i == 4):
                    continue
                yield (k, i, j)


def analyze(g, step, detail=False):
    fam, (u, v, x, y), (ei, fi) = g.families(step)
    S = fam["N10"]+fam["N01"]+fam["N11"]
    C0 = S[0]
    L = differences(S)
    L0 = sum((differences(fam[k]) for k in ("N10", "N01", "N11")), [])
    V = differences(fam["N00"])
    U = sum((differences(fam[k]) for k in ("Pux", "Pvy", "D11")), [])
    ef = add(g.unit(u, v), g.unit(x, y))
    b = add(fam["Pux"][0], fam["Pvy"][0], fam["D11"][0], scale(2, ef), scale(-3, C0))
    dg, rl, rlu = rank(differences(g.cycles())), rank(L), rank(L+U)
    out = dict(n=g.n, step=list(step), counts={k: len(vv) for k, vv in fam.items()},
               dg=dg, rankL=rl, rankU=rank(U), rankUV=rank(U+V),
               ell=dg-rl, t=rlu-rl, eta=rank(L+U+[b])-rlu)
    assert rank(L) == rank(L0)+2
    f = g.record["faces"][step[0]]
    i, j = step[1:]
    A = [u]+list(reversed(f[j+1:]+f[:i]))
    B = f[i+1:j+1]
    assert A[0] == u and A[-1] == x and B[0] == v and B[-1] == y
    out["arcs"] = [len(A)-1, len(B)-1]
    out["face_length"] = len(f)
    qA = add(*(scale((-1)**k, g.unit(a, z)) for k, (a, z) in enumerate(zip(A, A[1:]))))
    qB = add(*(scale((-1)**k, g.unit(a, z)) for k, (a, z) in enumerate(zip(B, B[1:]))))
    good, residual, class_info, toggles = [], [], {}, []
    if fam["N00"]:
        for key, q in (("Pux", qA), ("Pvy", qB), ("D11", add(qA, qB))):
            J = fam[key]
            F = [N for N in fam["N00"] if sub(N, q) in J]
            R = [P for P in J if add(P, q) not in fam["N00"]]
            anchor = sub(F[0], q) if F else J[0]
            E = [sub(P, anchor) for P in R]
            good += differences(F)
            residual += E
            assert rank(differences(J)) == rank(differences(F)+E)
            assert rank(differences(J)+differences(F)+E) == rank(differences(J))
            class_info[key] = dict(class_rank=rank(differences(J)), good_count=len(F),
                                   good_rank=rank(differences(F)), residual_count=len(R),
                                   residual_rank=rank(E), q=list(q))
            if out["arcs"] == [3, 3]:
                for N in fam["N00"]:
                    z = sub(N, q)
                    binary = all(a in (0, 1) for a in z)
                    middle = ([g.eid[edge(*A[1:3])]] if key == "Pux" else
                              [g.eid[edge(*B[1:3])]] if key == "Pvy" else
                              [g.eid[edge(*A[1:3])], g.eid[edge(*B[1:3])]])
                    assert binary == all(not N[k] for k in middle)
                    cs = g.components(z) if binary else ()
                    assert not binary or (2 <= len(cs) <= 4 if key == "D11" else 1 <= len(cs) <= 2)
                    toggles.append(dict(family=key, N=list(N), binary=binary,
                                        components=cs, compatible=z in J))
        assert rank(U+good+residual) == rank(U) == rank(good+residual)
        c = add(fam["N00"][0], scale(-1, fam["N10"][0]),
                scale(-1, fam["N01"][0]), fam["N11"][0])
        out.update(delta_V=rank(L0+V)-rank(L0+good),
                   delta_R=rank(L0+good+residual)-rank(L0+good),
                   epsilon=rank(L0+V+[c])-rank(L0+V), classes=class_info)
        assert out["ell"]-out["t"] == out["delta_V"]+out["epsilon"]-out["delta_R"]
    else:
        assert out["ell"] == 0
    if len(f) == 4:
        assert rank(U+V) == rank(U) == rank(V)
        s = sub(ef, add(g.unit(u, x), g.unit(v, y)))
        for N in fam["N00"]:
            F = add(N, s)
            assert F in g.factors and len(g.components(F)) == 2
        out["alpha"] = None
        if out["t"] == out["ell"]-1:
            r = sub(fam["N00"][0], C0)
            basis = int_basis(L+V)
            qr, qs = quotient(r, basis), quotient(s, basis)
            assert any(qr)
            k = next(k for k, z in enumerate(qr) if z)
            alpha = qs[k]/qr[k]
            if qs == scale(alpha, qr):
                assert rank(differences(g.cycles())+[s]) == dg
                out.update(alpha=str(alpha), weight=str(1+alpha),
                           primitive_pair=[alpha.denominator, alpha.numerator])
                assert quotient(b, basis) == add(scale(3, qr), scale(2, qs))
            else:
                out["alpha"] = "outside"
    if detail:
        return out, dict(families=fam, L=L, L0=L0, V=V, U=U, b=b,
                         C0=C0, arcs=[A, B], toggles=toggles)
    return out


def expand(record, step, label="I172"):
    g = Graph(record)
    fi, i, j = step
    f = record["faces"][fi]
    u, v, y, x = f[i], f[i+1], f[j], f[(j+1) % len(f)]
    p, q, r, s = range(max(g.vertices)+1, max(g.vertices)+5)
    replacements = {edge(u, v): (u, p, q, v), edge(x, y): (x, r, s, y)}
    faces = []
    for k, face in enumerate(record["faces"]):
        if k == fi:
            continue
        new = []
        for a, b in zip(face, face[1:]+face[:1]):
            path = replacements.get(edge(a, b))
            if path:
                path = path if path[0] == a else path[::-1]
                new.extend(path[:-1])
            else:
                new.append(a)
        faces.append(new)
    faces += [f[i+1:j+1]+[s, q], f[j+1:]+f[:i+1]+[p, r], [p, q, s, r]]
    es = set(g.edges)-set(replacements)
    for path in replacements.values():
        es.update(edge(a, b) for a, b in zip(path, path[1:]))
    es.update((edge(p, r), edge(q, s)))
    child = dict(n=g.n+4, edges=sorted(es), faces=faces,
                 history=record.get("history", "")+" "+label+"S"+str(list(step)))
    Graph(child).validate()
    return child

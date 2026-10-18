#!/usr/bin/env python3
"""MIT. Reviewer-side finite diagnostic for TREE097 (supplementary only).

Exact rational checks of finite combinatorial/algebraic identities used by the
candidate. No check here proves the universal theorem, the source analytic
inputs, DGLN, or the Bansal et al. tree lemma.
"""
import json, math, random, sys
from fractions import Fraction as F

def rational_unit(d, rng):
    # inverse stereographic projection of a rational point of R^{d-1}
    if d == 1:
        return [F(rng.choice([-1, 1]))]
    y = [F(rng.randint(-7, 7), rng.randint(1, 5)) for _ in range(d - 1)]
    s = sum(t * t for t in y)
    return [2 * t / (s + 1) for t in y] + [(s - 1) / (s + 1)]

def matvec(A, x): return [sum(a * b for a, b in zip(r, x)) for r in A]
def dot(a, b): return sum(x * y for x, y in zip(a, b))

# ---------- 1. filter algebra (Sections 3-4 of candidate) ----------
def filter_case(d, n, rng):
    bs, cs = [], []
    for _ in range(n):
        if rng.random() < 0.2:
            bs.append([F(0)] * d); cs.append(F(1)); continue
        t = F(rng.randint(1, 9), rng.randint(40, 90))  # |b| = 2t/(1+t^2) < 1/2
        r = 2 * t / (1 + t * t); u = rational_unit(d, rng)
        if bs and rng.random() < 0.2:
            bs.append(list(bs[-1])); cs.append(cs[-1]); continue  # repetition
        bs.append([r * x for x in u]); cs.append((1 - t * t) / (1 + t * t))
    m = d + n
    # R_i as d x m matrices
    R = [[F(int(i == j)) for j in range(m)] for i in range(d)]
    Rs = [R]
    etas = []
    for i, (b, c) in enumerate(zip(bs, cs)):
        assert dot(b, b) + c * c == 1 and c > 0
        eta = 1 / (1 + c); etas.append(eta)
        C = [[F(int(p == q)) - eta * b[p] * b[q] for q in range(d)] for p in range(d)]
        # C^2 + b b^T = I
        for p in range(d):
            for q in range(d):
                v = sum(C[p][k] * C[k][q] for k in range(d)) + b[p] * b[q]
                assert v == (1 if p == q else 0)
        newR = [[sum(C[p][k] * R[k][j] for k in range(d)) + (b[p] if j == d + i else 0)
                 for j in range(m)] for p in range(d)]
        R = newR; Rs.append(R)
    for Ri in Rs:  # R_i R_i^T = I_d
        for p in range(d):
            for q in range(d):
                assert dot(Ri[p], Ri[q]) == (1 if p == q else 0)
    # predictor rows m_i x = eta_i b_i^T R_{i-1} x^0 ; column bound <= max|b|^2
    M = []
    for i in range(n):
        row = [F(0)] * m
        for j in range(d, m):
            row[j] = etas[i] * sum(bs[i][p] * Rs[i][p][j] for p in range(d))
        assert all(row[j] == 0 for j in range(d + i, m))  # causality
        M.append(row)
    for j in range(m):
        col = sum(M[i][j] ** 2 for i in range(n))
        bound = dot(bs[j - d], bs[j - d]) if j >= d else 0
        assert col <= bound
    # x(eps), cancellation, injectivity, oddness
    seen = {}
    pats = [tuple(rng.choice([-1, 1]) for _ in range(n)) for _ in range(12)] if n > 6 else \
        [tuple(1 - 2 * ((k >> i) & 1) for i in range(n)) for k in range(2 ** n)]
    for eps in pats:
        x = [F(0)] * m
        for i in range(n):
            x[d + i] = eps[i] + dot(M[i], x)
        for t in range(n + 1):
            st = matvec(Rs[t], x)
            ps = [sum(eps[i] * bs[i][p] for i in range(t)) for p in range(d)]
            assert st == ps
        back = tuple(int(x[d + i] - dot(M[i], x)) for i in range(n))
        assert back == eps
        assert tuple(x) not in seen or seen[tuple(x)] == eps
        seen[tuple(x)] = eps
        neg = [F(0)] * m
        for i in range(n):
            neg[d + i] = -eps[i] + dot(M[i], neg)
        assert neg == [-v for v in x]
    return len(pats)

# ---------- 2. tree decompositions (Sections 5-6) ----------
def random_tree(rng, nv):
    par = [None]
    for v in range(1, nv):
        mode = rng.random()
        if mode < 0.5: p = v - 1                       # long unary stretches
        elif mode < 0.7: p = 0                          # high root degree
        else: p = rng.randrange(v)
        par.append(p)
    return par

def analyse_tree(par, d, rng):
    nv = len(par); ch = [[] for _ in range(nv)]
    for v in range(1, nv): ch[par[v]].append(v)
    leaves = [v for v in range(nv) if not ch[v]]; L = len(leaves)
    ell = [0] * nv
    for v in reversed(range(nv)):  # parents have smaller index
        ell[v] = 1 if not ch[v] else sum(ell[c] for c in ch[v])
    heavy = [max(ch[v], key=lambda c: (ell[c], -c)) if ch[v] else None for v in range(nv)]
    chain_of = [None] * nv; chains = []
    for v in range(nv):
        if v == 0 or heavy[par[v]] != v:
            cur = []; w = v
            while w is not None:
                chain_of[w] = len(chains); cur.append(w); w = heavy[w]
            chains.append(cur)
    assert sorted(c[-1] for c in chains) == sorted(leaves) and len(chains) == L
    K = int(math.floor(math.log2(L))) if L >= 1 else 0
    labels = [[F(rng.randint(-3, 3), 3) for _ in range(d)] for _ in range(nv)]
    eps = [rng.choice([-1, 1]) for _ in range(nv)]
    def path(v):
        p = []
        while v is not None: p.append(v); v = par[v]
        return p[::-1]
    def ssum(vs): return [sum(eps[u] * labels[u][k] for u in vs) for k in range(d)]
    neg_control_differs = 0
    for v in range(nv):
        P = path(v)
        light = sum(1 for u in P[1:] if heavy[par[u]] != u)
        assert light <= K and all(2 * ell[u] <= ell[par[u]] for u in P[1:] if heavy[par[u]] != u)
        h = chains[chain_of[v]][0]; anc = path(h)[:-1]
        pieces = []; term = []
        for u in anc:
            if not pieces or chain_of[u] != pieces[-1][0]:
                pieces.append((chain_of[u], [])); 
            pieces[-1][1].append(u)
        assert len(pieces) <= K and len({c for c, _ in pieces}) == len(pieces)
        for c, seg in pieces:
            assert seg == chains[c][:len(seg)]  # fixed initial (possibly internal) prefix
            term += chains[c]
        own = chains[chain_of[v]][:chains[chain_of[v]].index(v) + 1]
        assert ssum(P) == [a + b for a, b in zip(ssum([u for _, s in pieces for u in s]), ssum(own))]
        if ssum([u for _, s in pieces for u in s]) != ssum(term): neg_control_differs += 1
    # unary compression
    b = sum(1 for v in range(nv) if len(ch[v]) >= 2)
    starts = [v for v in range(nv) if v == 0 or len(ch[par[v]]) >= 2]
    uch = {}; uof = [None] * nv
    for s in starts:
        cur = [s]; w = s
        while len(ch[w]) == 1: w = ch[w][0]; cur.append(w)
        for u in cur: uof[u] = s
        uch[s] = cur
    assert all(u is not None for u in uof) and len(uch) == L + b and L + b <= 2 * L - 1
    assert sum(len(ch[v]) - 1 for v in range(nv) if len(ch[v]) >= 2) == L - 1
    tau = {s: rng.choice([-1, 1]) for s in starts}
    for v in range(nv):
        P = path(v); C = uch[uof[v]]; anc_chains = []
        for u in P[:P.index(C[0])]:
            if not anc_chains or uof[u] != anc_chains[-1]: anc_chains.append(uof[u])
        tot = [F(0)] * d
        for s in anc_chains:  # complete strict-ancestor chains
            assert all(u in P for u in uch[s]) and uch[s][-1] in P
            tot = [a + tau[s] * x for a, x in zip(tot, ssum(uch[s]))]
        tot = [a + tau[C[0]] * x for a, x in zip(tot, ssum(C[:C.index(v) + 1]))]
        signed = [sum(tau[uof[u]] * eps[u] * labels[u][k] for u in P) for k in range(d)]
        assert signed == tot
    return L, b, neg_control_differs

def main():
    rng = random.Random(20261017)
    fil = 0
    for (d, n) in [(1, 6), (2, 6), (3, 5), (4, 9), (2, 11)]:
        fil += filter_case(d, n, rng)
    trees = 0; negs = 0; maxL = 0
    for k in range(400):
        par = random_tree(rng, rng.randint(1, 40))
        L, b, nd = analyse_tree(par, rng.randint(1, 3), rng)
        trees += 1; negs += nd; maxL = max(maxL, L)
    # scalar inequalities used in MGF and net steps
    for k in range(1, 400):
        x = k / 40
        assert 2 * math.exp(x) - 1 <= math.exp(2 * x)
    for k in range(1, 30):
        assert math.factorial(2 * k) >= math.factorial(k) ** 2
    a = None
    lo, hi = 0.0, 3.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if 0.5 * (1 + math.erf(mid / math.sqrt(2))) < 2 / 3: lo = mid
        else: hi = mid
    a = lo
    assert abs(math.erf(a / math.sqrt(2)) - 1 / 3) < 1e-12  # P(|g|<=a)=1/3
    assert math.erf((1 / 5) / math.sqrt(2)) < 0.5  # slab of half-width 1/5 below 1/2
    res = {"status": "PASS", "filter_sign_patterns": fil, "random_trees": trees,
           "max_leaves": maxL, "internal_vs_terminal_prefix_differences": negs,
           "a_Phi_inv_2_3": a, "H_G_value": 6 / a ** 2 + 1.5,
           "scope": "Finite exact identities only; supplementary, not proof."}
    print(json.dumps(res, sort_keys=True))

if __name__ == "__main__":
    try: main()
    except AssertionError as e:
        print("FAIL", repr(e), file=sys.stderr); sys.exit(1)

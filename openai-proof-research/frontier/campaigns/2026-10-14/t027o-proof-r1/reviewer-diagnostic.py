#!/usr/bin/env python3
"""MIT. Independent T027O reviewer diagnostic. Finite-field rank checks only; not a proof.

Written by the T027O proof reviewer without reusing author scripts. Eigenvalues of C are
reductions of eta*alpha_i, alpha_i the roots of X^r-3X^(r-1)-1, modulo primes where it splits.
"""
import json, random

def is_prime(p): return p > 1 and all(p % q for q in range(2, int(p ** .5) + 1))

class F:
    def __init__(s, p, r): s.p, s.r = p, r
    def eye(s): return [[int(i == j) for j in range(s.r)] for i in range(s.r)]
    def zero(s): return [[0] * s.r for _ in range(s.r)]
    def mul(s, a, b):
        p, r = s.p, s.r
        bt = list(zip(*b))
        return [[sum(x * y for x, y in zip(row, col)) % p for col in bt] for row in a]
    def add(s, a, b, c=1): return [[(x + c * y) % s.p for x, y in zip(u, v)] for u, v in zip(a, b)]
    def sc(s, a, c): return [[x * c % s.p for x in row] for row in a]
    def tr(s, a): return sum(a[i][i] for i in range(s.r)) % s.p
    def inv(s, a):
        p, n = s.p, s.r
        w = [a[i][:] + s.eye()[i] for i in range(n)]
        for i in range(n):
            j = next(j for j in range(i, n) if w[j][i] % p)
            w[i], w[j] = w[j], w[i]
            t = pow(w[i][i], -1, p); w[i] = [x * t % p for x in w[i]]
            for j in range(n):
                if j != i and w[j][i]:
                    t = w[j][i]; w[j] = [(x - t * y) % p for x, y in zip(w[j], w[i])]
        return [row[n:] for row in w]
    def diag(s, v): return [[v[i] if i == j else 0 for j in range(s.r)] for i in range(s.r)]

def rank(rows, p):
    a = [row[:] for row in rows if any(x % p for x in row)]
    if not a: return 0
    r = 0; ncol = len(a[0])
    for j in range(ncol):
        k = next((k for k in range(r, len(a)) if a[k][j] % p), None)
        if k is None: continue
        a[k], a[r] = a[r], a[k]; t = pow(a[r][j], -1, p); a[r] = [x * t % p for x in a[r]]
        for k in range(len(a)):
            if k != r and a[k][j]:
                t = a[k][j]; a[k] = [(x - t * y) % p for x, y in zip(a[k], a[r])]
        r += 1
        if r == len(a): break
    return r

def sl_basis(r):
    out = []
    for i in range(r):
        for j in range(r):
            if i != j: out.append(('off', i, j))
    for i in range(r - 1): out.append(('diag', i, r - 1))
    return out

def pair(M, e, p):
    """tr(M E) for basis element E."""
    kind, i, j = e
    return M[j][i] % p if kind == 'off' else (M[i][i] - M[j][j]) % p

def basis_matrix(f, e):
    E = f.zero(); kind, i, j = e
    if kind == 'off': E[i][j] = 1
    else: E[i][i] = 1; E[j][j] = f.p - 1
    return E

def esym(f, W):
    """elementary symmetric functions e_0..e_r of eigenvalues via Faddeev-LeVerrier."""
    p, r = f.p, f.r
    e = [1]; Mk = f.zero(); powers = [f.eye()]
    for k in range(1, r + 1): powers.append(f.mul(powers[-1], W))
    ptr = [f.tr(powers[k]) for k in range(r + 1)]
    for k in range(1, r + 1):
        s = sum((-1) ** (i - 1) * e[k - i] * ptr[i] for i in range(1, k + 1)) % p
        e.append(s * pow(k, -1, p) % p)
    return e, powers

def grad_e(f, W, j):
    e, powers = esym(f, W)
    G = f.zero()
    for i in range(j):
        G = f.add(G, f.sc(powers[i], ((-1) ** i) * e[j - 1 - i] % f.p))
    return G

def word_mats(f, rho, word):
    mats = []
    for g, s in word:
        mats.append(rho[g] if s == 1 else f.inv(rho[g]))
    return mats

def prod(f, mats):
    out = f.eye()
    for m in mats: out = f.mul(out, m)
    return out

def func_rows(f, rho, word, ngen, basis):
    """Rows: derivatives of e_1..e_(r-1) of word, columns: generator x basis, variation x->x(I+eps E)."""
    mats = word_mats(f, rho, word); W = prod(f, mats)
    n = len(mats)
    pre = [f.eye()]
    for m in mats: pre.append(f.mul(pre[-1], m))
    suf = [f.eye()]
    for m in reversed(mats): suf.append(f.mul(m, suf[-1]))
    suf = list(reversed(suf))  # suf[i] = mats[i]...mats[n-1]
    rows = []
    for j in range(1, f.r):
        G = grad_e(f, W, j)
        cols = [[0] * len(basis) for _ in range(ngen)]
        for pos, (g, s) in enumerate(word):
            P0 = pre[pos]; S1 = suf[pos + 1]
            if s == 1:
                M = f.mul(f.mul(f.mul(S1, G), P0), rho[g])
                sign = 1
            else:
                M = f.mul(f.mul(f.mul(f.inv(rho[g]), S1), G), P0)
                sign = -1
            for b, e in enumerate(basis):
                cols[g][b] = (cols[g][b] + sign * pair(M, e, f.p)) % f.p
        rows.append([x for g in range(ngen) for x in cols[g]])
    return rows

def relation_rows(f, rho, word, ngen, basis):
    mats = word_mats(f, rho, word); n = len(mats)
    pre = [f.eye()]
    for m in mats: pre.append(f.mul(pre[-1], m))
    suf = [f.eye()]
    for m in reversed(mats): suf.append(f.mul(m, suf[-1]))
    suf = list(reversed(suf))
    cols = []
    for g in range(ngen):
        for e in basis:
            E = basis_matrix(f, e); D = f.zero()
            for pos, (h, s) in enumerate(word):
                if h != g: continue
                if s == 1: term = f.mul(f.mul(pre[pos], f.mul(rho[g], E)), suf[pos + 1])
                else: term = f.sc(f.mul(f.mul(pre[pos], f.mul(E, f.inv(rho[g]))), suf[pos + 1]), f.p - 1)
                D = f.add(D, term)
            cols.append([D[i][j] for i in range(f.r) for j in range(f.r)])
    return [list(r) for r in zip(*cols)]

def W(s):
    """parse word like 'a b A c' (capital = inverse); generator names map later."""
    return s.split()

def build(f, g, rng, mu):
    p, r = f.p, f.r
    # random Q in SL_r(F_p): product of elementary matrices
    Q = f.eye()
    for _ in range(6 * r * r):
        i, j = rng.sample(range(r), 2); E = f.eye(); E[i][j] = rng.randrange(1, p); Q = f.mul(Q, E)
    m = [rng.randrange(1, 6) for _ in range(r - 1)]
    bd = [pow(mu[i], m[i], p) for i in range(r - 1)]
    last = 1
    for i in range(r - 1): last = last * pow(mu[i], -m[i] % (p - 1), p) % p
    B = f.diag(bd + [last])
    av = [rng.randrange(2, p) for _ in range(r - 1)]
    t = 1
    for x in av: t = t * x % p
    A = f.diag(av + [pow(t, -1, p)])
    C = f.mul(f.mul(Q, f.diag(mu)), f.inv(Q))
    names = ['a', 'b', 'c', 'd'] + [x + str(i) for i in range(3, g + 1) for x in ('a', 'b')]
    rho = {'a': A, 'b': B, 'c': C, 'd': f.eye()}
    for i in range(3, g + 1): rho['a' + str(i)] = f.eye(); rho['b' + str(i)] = f.eye()
    return names, rho, A, B, C, Q, m

def to_idx(names, toks):
    out = []
    for t in toks:
        inv = t[0].isupper(); base = t[0].lower() + t[1:]
        out.append((names.index(base), -1 if inv else 1))
    return out

def u0(k, l): return ['b'] + ['a'] * k + ['d'] + ['c'] * l
def u1(k, l): return ['a', 'b'] + ['a'] * (k - 1) + ['c', 'd'] + ['c'] * (l - 1)

def residual_system_kernel(f, A, C, Q):
    """dim of {S in sl_r : (Ad_A-Ad_C)S=0, (I-Ad_C)S in h+h_C} with h cap h_C check."""
    p, r = f.p, f.r; basis = sl_basis(r); Ai = f.inv(A); Ci = f.inv(C); Qi = f.inv(Q)
    hb = [('diag', i, r - 1) for i in range(r - 1)]
    cols = []
    for e in basis:
        S = basis_matrix(f, e)
        x = f.add(f.mul(f.mul(A, S), Ai), f.mul(f.mul(C, S), Ci), -1)
        y = f.add(S, f.mul(f.mul(C, S), Ci), -1)
        cols.append([v for row in x for v in row] + [v for row in y for v in row])
    for e in hb:
        H = basis_matrix(f, e)
        cols.append([0] * (r * r) + [(-v) % p for row in H for v in row])
    for e in hb:
        H = f.mul(f.mul(Q, basis_matrix(f, e)), Qi)
        cols.append([0] * (r * r) + [(-v) % p for row in H for v in row])
    rows = [list(t) for t in zip(*cols)]
    return len(cols) - rank(rows, p)

def p1_p2(f, Q, rng):
    p, r = f.p, f.r; Qi = f.inv(Q)
    hC = [f.mul(f.mul(Q, basis_matrix(f, ('diag', i, r - 1))), Qi) for i in range(r - 1)]
    p1 = all(rank([[K[i][j] for K in hC], [K[j][i] for K in hC]], p) == 2
             for i in range(r) for j in range(i + 1, r))
    t = [rng.randrange(2, p) for _ in range(r - 1)]; z = 1
    for x in t: z = z * x % p
    N = f.mul(f.mul(Q, f.diag(t + [pow(z, -1, p)])), Qi)
    off = all(N[i][j] for i in range(r) for j in range(r) if i != j)
    tri = all((N[i][j] * N[j][k] * N[k][i] - N[i][k] * N[k][j] * N[j][i]) % p
              for i in range(r) for j in range(r) for k in range(r) if len({i, j, k}) == 3)
    return p1, off and tri

def tangent_case(r, g, p, mu, seed):
    f = F(p, r); rng = random.Random(seed)
    names, rho, A, B, C, Q, m = build(f, g, rng, mu)
    basis = sl_basis(r); ngen = 2 * g; d = r * r - 1
    rlist = [rho[n] for n in names]
    rel = ['a', 'b', 'A', 'B', 'c', 'd', 'C', 'D']
    for i in range(3, g + 1): rel += ['a%d' % i, 'b%d' % i, 'A%d' % i, 'B%d' % i]
    R = relation_rows(f, rlist, to_idx(names, rel), ngen, basis)
    fam = {'a': [['a']], 'c': [['c']], 'u0': [u0(k, l) for k in range(1, r + 1) for l in range(1, r + 1)],
           'u1': [u1(k, l) for k in range(1, r + 1) for l in range(1, r + 1)], 'extra': []}
    for i in range(3, g + 1):
        for k in range(1, r + 1):
            for l in range(1, r + 1):
                fam['extra'].append(u1(k, l) + ['a%d' % i]); fam['extra'].append(u1(k, l) + ['B%d' % i])
    rows = {key: [row for w in ws for row in func_rows(f, rlist, to_idx(names, w), ngen, basis)] for key, ws in fam.items()}
    total = ngen * d
    def kernel(keys):
        return total - rank(R + [row for k in keys for row in rows[k]], p)
    out = {'r': r, 'g': g, 'p': p, 'mu_mod_p': mu, 'B_exponents': m,
           'relation_rank': rank(R, p), 'expected_relation_rank': d,
           'kernel_full_family': kernel(['a', 'c', 'u0', 'u1', 'extra']),
           'expected_kernel_conjugation_dim': d,
           'kernel_without_u1': kernel(['a', 'c', 'u0', 'extra']),
           'kernel_without_u0': kernel(['a', 'c', 'u1', 'extra']),
           'residual_system_kernel': residual_system_kernel(f, A, C, Q)}
    out['P1'], out['P2_witness_found'] = p1_p2(f, Q, rng)
    if g >= 3: out['kernel_without_extra_curves'] = kernel(['a', 'c', 'u0', 'u1'])
    return out

def free_reduce(w):
    out = []
    for t in w:
        if out and out[-1] == (t.swapcase() if len(t) == 1 else None): out.pop()
        else: out.append(t)
    return out

def apply_auto(word, sub):
    res = []
    for t in word:
        if t.lower() in sub:
            img = sub[t.lower()]
            if t.isupper(): img = [x.swapcase() for x in reversed(img)]
            res += img
        else: res.append(t)
    return free_reduce(res)

def automorphism_checks():
    rel = list('abABcdCD'); out = {}
    for m in range(1, 5):
        for n in range(1, 5):
            out['b->ba^%d,d->dc^%d' % (m, n)] = apply_auto(rel, {'b': ['b'] + ['a'] * m, 'd': ['d'] + ['c'] * n}) == rel
    out['a->ab'] = apply_auto(rel, {'a': ['a', 'b']}) == rel
    ok_words = True
    for k in range(1, 5):
        for l in range(1, 5):
            ok_words &= apply_auto(list('bd'), {'b': ['b'] + ['a'] * k, 'd': ['d'] + ['c'] * l}) == free_reduce(u0(k, l))
            ok_words &= apply_auto(list('abcd'), {'b': ['b'] + ['a'] * (k - 1), 'd': ['d'] + ['c'] * (l - 1)}) == free_reduce(u1(k, l))
    out['images_equal_u0_u1_k_l_le_4'] = ok_words
    return out

def ribbon_checks(gmax=5):
    """One-vertex ribbon graph, half-edges: x = start of x, X = end of x."""
    res = {}
    for g in range(2, gmax + 1):
        gens = ['a', 'b', 'c', 'd'] + [x + str(i) for i in range(3, g + 1) for x in ('a', 'b')]
        order = []
        for i in range(g):
            x, y = gens[2 * i], gens[2 * i + 1]
            order += [x, y.upper() if len(y) == 1 else y[0].upper() + y[1:], x.upper() if len(x) == 1 else x[0].upper() + x[1:], y]
        pos = {h: i for i, h in enumerate(order)}
        def opp(h): return h[0].swapcase() + h[1:]
        n = len(order); seen = set(); cycles = []
        for h0 in order:
            if h0 in seen: continue
            cyc = []; h = h0
            while h not in seen:
                seen.add(h); cyc.append(h); h = order[(pos[opp(h)] + 1) % n]
            cycles.append(cyc)
        boundary = cycles[0] if len(cycles) == 1 else None
        def turns(word):
            return [(opp(word[i]), word[(i + 1) % len(word)]) for i in range(len(word))]
        def noncross(word):
            ch = [tuple(sorted((pos[x], pos[y]))) for x, y in turns(word)]
            used = [h for c in turns(word) for h in c]
            if len(used) != len(set(used)): return False
            for (a1, b1) in ch:
                for (a2, b2) in ch:
                    if (a1, b1) < (a2, b2) and ((a1 < a2 < b1) != (a1 < b2 < b1)): return False
            return True
        words = {'bd': ['b', 'd'], 'abcd': ['a', 'b', 'c', 'd']}
        for i in range(3, g + 1):
            words['abcd a%d' % i] = ['a', 'b', 'c', 'd', 'a%d' % i]
            words['abcd B%d' % i] = ['a', 'b', 'c', 'd', 'B%d' % i]
        res[g] = {'one_boundary': len(cycles) == 1, 'boundary_word': boundary,
                  'noncrossing': {k: noncross(v) for k, v in words.items()}}
    return res

def negative_controls():
    """Checker must report failure when a hypothesis is removed."""
    r, g, p, mu = 3, 2, 1069, [579, 629, 933]
    f = F(p, r); rng = random.Random(7)
    names, rho, A, B, C, Q, m = build(f, g, rng, mu)
    I = f.eye(); Cd = f.diag(mu)
    rlist = [A, B, Cd, I]
    basis = sl_basis(r); d = r * r - 1
    R = relation_rows(f, rlist, to_idx(names, ['a', 'b', 'A', 'B', 'c', 'd', 'C', 'D']), 4, basis)
    words = [['a'], ['c']] + [u0(k, l) for k in range(1, 4) for l in range(1, 4)] + [u1(k, l) for k in range(1, 4) for l in range(1, 4)]
    rows = [row for w in words for row in func_rows(f, rlist, to_idx(names, w), 4, basis)]
    out = {'Q_identity_residual_kernel': residual_system_kernel(f, A, Cd, I),
           'Q_identity_relation_rank': rank(R, p),
           'Q_identity_family_kernel': 4 * d - rank(R + rows, p)}
    # a word whose turn chords cross in this ribbon order; the checker must not certify it
    order = ['a', 'B', 'A', 'b', 'c', 'D', 'C', 'd']; pos = {h: i for i, h in enumerate(order)}
    tw = [('A', 'd'), ('D', 'b'), ('B', 'c'), ('C', 'a')]
    ch = [tuple(sorted((pos[x], pos[y]))) for x, y in tw]
    out['adbc_chords_cross'] = any((a1 < a2 < b1) != (a1 < b2 < b1) for (a1, b1) in ch for (a2, b2) in ch if (a1, b1) < (a2, b2))
    out['expected'] = out['Q_identity_residual_kernel'] > 0 and out['Q_identity_family_kernel'] > d and out['adbc_chords_cross']
    return out

def main():
    cases = []
    specs = [(3, 2, 1069, [579, 629, 933], 1), (3, 2, 1097, [114, 488, 498], 2), (3, 3, 1069, [579, 629, 933], 3),
             (4, 2, 1481, None, 4), (4, 3, 1481, None, 5), (5, 2, 1009, [351, 576, 675, 710, 718], 6)]
    for r, g, p, roots, seed in specs:
        if roots is None:
            f = lambda x: (pow(x, r, p) - 3 * pow(x, r - 1, p) - 1) % p
            roots = [x for x in range(p) if f(x) == 0]
            eta = next(x for x in range(2, p) if pow(x, 4, p) == p - 1)
            mu = [eta * a % p for a in roots]
        else:
            mu = roots[:]
        prod_mu = 1
        for x in mu: prod_mu = prod_mu * x % p
        assert prod_mu == 1 and len(set(mu)) == r, (r, mu)
        cases.append(tangent_case(r, g, p, mu, seed))
    out = {'status': 'DIAGNOSTIC_ONLY', 'cases': cases, 'automorphisms': automorphism_checks(), 'ribbon': ribbon_checks(),
           'negative_controls': negative_controls()}
    ok = all(c['relation_rank'] == c['expected_relation_rank'] and c['kernel_full_family'] == c['expected_kernel_conjugation_dim']
             and c['residual_system_kernel'] == 0 and c['P1'] and c['P2_witness_found'] for c in cases)
    ok &= all(out['automorphisms'].values())
    ok &= all(v['one_boundary'] and all(v['noncrossing'].values()) for v in out['ribbon'].values())
    ok &= out['negative_controls']['expected']
    out['all_expected'] = ok
    print(json.dumps(out, indent=1))

if __name__ == '__main__': main()

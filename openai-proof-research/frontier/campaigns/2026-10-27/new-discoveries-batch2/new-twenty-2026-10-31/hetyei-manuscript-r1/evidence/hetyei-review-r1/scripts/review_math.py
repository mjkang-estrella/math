#!/usr/bin/env python3
"""Independent reviewer implementation (hetyei-review-r1). Written from the source definitions
(arXiv:2007.07362 Sec. 5 = DCG Sec. 6; Ehrenborg-Readdy Def. 9.1); does NOT import the discovery lane.

Usage: review_math.py LOGFILE SUBCOMMAND [ARGS]
  validate NMAX        poset-level validation of M (products) and I2 (brute-force interval transform),
                       both readings; full operator pinning via doubled chains up to degree NMAX
  kernel NMIN NMAX     exact ranks/kernels of I2 on degree n, both readings
  cert                 verify the lane's 20-term certificate u at n = 5, both readings
  srcvalues NMAX       checks against values/claims stated in the source (Boolean eigen, I2(c^n), M symmetric,
                       Cor 33, Cor 37/Prop 5.12 multiplicativity)
  eigen NMAX           347231: eigenvectors in S_n, compositions of Pyr and L, Lemma 36
Readings: 'ER'      M_{2,1,2}(u,v) = v.b.u (Ehrenborg-Readdy Def. 9.1)
          'PRINTED' M_{2,1,2}(u,v) = u.b.v (as printed in Hetyei Def. 5.6 / 31)
"""
import itertools, os, random, sys
from fractions import Fraction
from functools import lru_cache

LOG = None
def out(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.write(s + '\n'); LOG.flush()

# ---------------- ab-polynomials: dict word(str over 'ab') -> int/Fraction ----------------
def padd(p, q, c=1):
    r = dict(p)
    for w, x in q.items():
        r[w] = r.get(w, 0) + c * x
        if r[w] == 0:
            del r[w]
    return r

def pmulw(pre, p, post=''):
    return {pre + w + post: x for w, x in p.items()}

def pmul(p, q):
    r = {}
    for w1, x1 in p.items():
        for w2, x2 in q.items():
            w = w1 + w2
            r[w] = r.get(w, 0) + x1 * x2
            if r[w] == 0:
                del r[w]
    return r

def star(p):
    return {w[::-1]: x for w, x in p.items()}

def scal(c, p):
    return {w: c * x for w, x in p.items() if c * x != 0}

def cop(w):
    """Ehrenborg-Readdy coproduct on a word: sum_i w1..w_{i-1} (x) w_{i+1}..w_n (Hetyei Def. 4.6)."""
    return [(w[:i], w[i + 1:]) for i in range(len(w))]

# ---------------- mixing operator (Hetyei Def. 5.6 / ER Def. 9.1) ----------------
@lru_cache(maxsize=None)
def Mrs(r, s, n, u, v, reading):
    """M_{r,s,n}(u,v) on words; returns tuple of (word, coeff) items."""
    if n < 2 or (n - r - s - 1) % 2 != 0:
        return ()
    if n == 2:
        if (r, s) == (1, 2):
            return ((u + 'a' + v, 1),)
        if (r, s) == (2, 1):
            return (((v + 'b' + u) if reading == 'ER' else (u + 'b' + v)), 1),
        return ()
    res = {}
    if r == 1:
        for u1, u2 in cop(u):
            for w, x in Mrs(2, s, n - 1, u2, v, reading):
                ww = u1 + 'a' + w
                res[ww] = res.get(ww, 0) + x
    else:
        for v1, v2 in cop(v):
            for w, x in Mrs(1, s, n - 1, u, v2, reading):
                ww = v1 + 'b' + w
                res[ww] = res.get(ww, 0) + x
    return tuple((w, x) for w, x in sorted(res.items()) if x)

@lru_cache(maxsize=None)
def Mw(u, v, reading):
    res = {}
    for r in (1, 2):
        for s in (1, 2):
            for n in range(2, len(u) + len(v) + 3):
                for w, x in Mrs(r, s, n, u, v, reading):
                    res[w] = res.get(w, 0) + x
    # sanity: nothing beyond the bound (each recursion step consumes one letter)
    for r in (1, 2):
        for s in (1, 2):
            for n in range(len(u) + len(v) + 3, len(u) + len(v) + 6):
                assert not Mrs(r, s, n, u, v, reading)
    return tuple((w, x) for w, x in sorted(res.items()) if x)

def M(p, q, reading):
    res = {}
    for u, x in p.items():
        for v, y in q.items():
            for w, z in Mw(u, v, reading):
                res[w] = res.get(w, 0) + x * y * z
    return {w: x for w, x in res.items() if x}

# ---------------- I2 (Hetyei Thm 5.7 / 32) ----------------
@lru_cache(maxsize=None)
def I2w(w, reading):
    res = {w: 1}
    res = padd(res, {w[::-1]: 1})
    for u1, u2 in cop(w):
        res = padd(res, dict(Mw(u1[::-1], u2, reading)))
    return tuple(sorted(res.items()))

def I2(p, reading):
    res = {}
    for w, x in p.items():
        for ww, y in I2w(w, reading):
            res[ww] = res.get(ww, 0) + x * y
    return {w: x for w, x in res.items() if x}

def words(n):
    return [''.join(t) for t in itertools.product('ab', repeat=n)]

# ---------------- posets ----------------
class Poset:
    """Finite graded poset with 0hat (index 0) and 1hat; le[i][j] True iff i <= j; rk ranks."""
    def __init__(self, n, le, rk, name=''):
        self.n, self.le, self.rk, self.name = n, le, rk, name
        self.bot = next(i for i in range(n) if all(le[i][j] for j in range(n)))
        self.top = next(i for i in range(n) if all(le[j][i] for j in range(n)))
        self.rank = rk[self.top] - rk[self.bot]
        # check gradedness: covers raise rank by exactly 1
        for i in range(n):
            for j in range(n):
                if le[i][j] and i != j:
                    assert rk[j] > rk[i]
                    if not any(le[i][k] and le[k][j] and k not in (i, j) for k in range(n)):
                        assert rk[j] == rk[i] + 1, (name, i, j)

def poset_from_covers(n, covers, name=''):
    le = [[i == j for j in range(n)] for i in range(n)]
    for i, j in covers:
        le[i][j] = True
    for k in range(n):
        for i in range(n):
            if le[i][k]:
                for j in range(n):
                    if le[k][j]:
                        le[i][j] = True
    # ranks: longest chain from bottom
    bot = next(i for i in range(n) if all(le[i][j] for j in range(n)))
    order = sorted(range(n), key=lambda i: sum(le[j][i] for j in range(n)))
    rk = [0] * n
    for i in order:
        rk[i] = max([rk[j] + 1 for j in range(n) if le[j][i] and j != i] or [0])
    return Poset(n, le, rk, name)

def poset_from_le(elems, lefun, name=''):
    n = len(elems)
    le = [[lefun(elems[i], elems[j]) for j in range(n)] for i in range(n)]
    bot = next(i for i in range(n) if all(le[i][j] for j in range(n)))
    order = sorted(range(n), key=lambda i: sum(le[j][i] for j in range(n)))
    rk = [0] * n
    for i in order:
        rk[i] = max([rk[j] + 1 for j in range(n) if le[j][i] and j != i] or [0])
    return Poset(n, le, rk, name)

def flag_f(P):
    """dict frozenset(S) -> number of chains 0hat < x1 < ... < xk < 1hat with rank set S (relative ranks)."""
    n = P.n; bot, top = P.bot, P.top
    r0 = P.rk[bot]
    f = {}
    up = [[j for j in range(n) if P.le[i][j] and j != i and j != top] for i in range(n)]
    def dfs(i, S):
        f[S] = f.get(S, 0) + 1
        for j in up[i]:
            dfs(j, S | {P.rk[j] - r0})
    dfs(bot, frozenset())
    return f

def psi(P):
    """ab-index: Psi = sum_S f_S prod_i (b if i in S else (a-b)), i = 1..rank-1 (Hetyei Sec. 1)."""
    m = P.rank - 1
    f = flag_f(P)
    res = {}
    for S, c in f.items():
        poly = {'': 1}
        for i in range(1, m + 1):
            poly = pmul(poly, {'b': 1} if i in S else {'a': 1, 'b': -1})
        res = padd(res, poly, c)
    return res

def chain(k):
    return poset_from_covers(k + 1, [(i, i + 1) for i in range(k)], f'chain{k}')

def boolean(k):
    el = list(range(1 << k))
    return poset_from_le(el, lambda x, y: x & y == x, f'B{k}')

def product(P, Q):
    el = [(i, j) for i in range(P.n) for j in range(Q.n)]
    return poset_from_le(el, lambda x, y: P.le[x[0]][y[0]] and Q.le[x[1]][y[1]], f'({P.name}x{Q.name})')

def dual(P):
    el = list(range(P.n))
    return poset_from_le(el, lambda x, y: P.le[y][x], f'{P.name}*')

def doubled_chain(m, S):
    """rank m+1 poset: 0hat, levels 1..m with 2 elements if i in S else 1, 1hat; all cross-level comparabilities."""
    el = [(0, 0)] + [(i, t) for i in range(1, m + 1) for t in range(2 if i in S else 1)] + [(m + 1, 0)]
    return poset_from_le(el, lambda x, y: x == y or x[0] < y[0], f'D{m}{sorted(S)}')

def face_lattice(facets, name):
    facets = [frozenset(F) for F in facets]
    V = frozenset().union(*facets)
    faces = {V, frozenset()}
    frontier = set(facets)
    faces |= frontier
    while frontier:
        new = set()
        for A in frontier:
            for F in facets:
                C = A & F
                if C not in faces:
                    new.add(C)
        faces |= new
        frontier = new
    faces |= {frozenset([v]) for v in V}
    el = sorted(faces, key=lambda s: (len(s), sorted(s)))
    return poset_from_le(el, lambda x, y: x <= y, name)

def random_graded(seed, rank, width):
    rng = random.Random(seed)
    levels = [[0]]
    idx = 1
    for r in range(1, rank):
        k = rng.randint(1, width)
        levels.append(list(range(idx, idx + k))); idx += k
    levels.append([idx]); idx += 1
    covers = []
    for r in range(1, rank + 1):
        lo, hi = levels[r - 1], levels[r]
        for y in hi:  # every element covers something
            for x in rng.sample(lo, rng.randint(1, len(lo))):
                covers.append((x, y))
        for x in lo:  # every element is covered
            if not any(c[0] == x for c in covers if c[1] in hi):
                covers.append((x, rng.choice(hi)))
    return poset_from_covers(idx, covers, f'rand{seed}r{rank}')

def interval_transform2_psi(P):
    """Brute force: sum over x in P of Psi of {[y,z] in I(P): y <= x <= z} ordered by inclusion
    (Hetyei Def. 5.1, Cor. 5.3, Def. 5.4), built directly from intervals."""
    n = P.n
    total = {}
    for x in range(n):
        el = [(y, z) for y in range(n) for z in range(n) if P.le[y][x] and P.le[x][z]]
        Q = poset_from_le(el, lambda s, t: P.le[t[0]][s[0]] and P.le[s[1]][t[1]], f'I2({P.name})@{x}')
        assert Q.rank == P.rank
        total = padd(total, psi(Q))
    return total

def test_posets():
    Ps = [chain(k) for k in range(1, 6)] + [boolean(k) for k in range(1, 5)]
    for k in range(3, 7):
        Ps.append(face_lattice([[i, (i + 1) % k] for i in range(k)], f'{k}-gon'))
    Ps.append(face_lattice([[0, 1, 2, 3], [0, 1, 4], [1, 2, 4], [2, 3, 4], [3, 0, 4]], 'sqpyramid'))
    Ps.append(face_lattice([[0, 1, 2], [3, 4, 5], [0, 1, 4, 3], [1, 2, 5, 4], [2, 0, 3, 5]], 'prism'))
    cube = [[v for v in range(8) if (v >> i) & 1 == t] for i in range(3) for t in (0, 1)]
    Ps.append(face_lattice(cube, 'cube'))
    octa = [[i, j, k] for i in (0, 1) for j in (2, 3) for k in (4, 5)]
    Ps.append(face_lattice(octa, 'octahedron'))
    for seed in range(12):
        Ps.append(random_graded(1000 + seed, 2 + seed % 4, 3))
    return Ps

# ---------------- exact linear algebra ----------------
def rank_exact(rows):
    """rank over Q of an integer/Fraction matrix (list of lists), fraction-free style via Fractions."""
    A = [[Fraction(x) for x in r] for r in rows]
    if not A:
        return 0
    m, ncol = len(A), len(A[0])
    rk = 0
    for c in range(ncol):
        piv = next((i for i in range(rk, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][c]
        for i in range(rk + 1, m):
            if A[i][c] != 0:
                f = A[i][c] / pv
                Ai, Ar = A[i], A[rk]
                for j in range(c, ncol):
                    if Ar[j]:
                        Ai[j] -= f * Ar[j]
        rk += 1
        if rk == m:
            break
    return rk

def nullspace(rows, ncol):
    """basis of {x : rows . x = 0} over Q (rows: list of lists)."""
    A = [[Fraction(x) for x in r] for r in rows]
    m = len(A)
    pivcols = []
    rk = 0
    for c in range(ncol):
        piv = next((i for i in range(rk, m) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        pv = A[rk][c]
        A[rk] = [x / pv for x in A[rk]]
        for i in range(m):
            if i != rk and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[rk][j] for j in range(ncol)]
        pivcols.append(c)
        rk += 1
    free = [c for c in range(ncol) if c not in pivcols]
    basis = []
    for fc in free:
        x = [Fraction(0)] * ncol
        x[fc] = Fraction(1)
        for i, pc in enumerate(pivcols):
            x[pc] = -A[i][fc]
        basis.append(x)
    return basis

def matrix_of(n, reading, basis_polys=None):
    """columns = images of basis polys (default: words), rows indexed by words of degree n."""
    W = words(n)
    idx = {w: i for i, w in enumerate(W)}
    B = basis_polys if basis_polys is not None else [{w: 1} for w in W]
    rows = [[0] * len(B) for _ in W]
    for j, p in enumerate(B):
        for w, x in I2(p, reading).items():
            rows[idx[w]][j] += x
    return rows

def sym_basis(n):
    seen, B = set(), []
    for w in words(n):
        if w in seen:
            continue
        seen |= {w, w[::-1]}
        B.append({w: 1} if w == w[::-1] else {w: 1, w[::-1]: 1})
    return B

def anti_basis(n):
    seen, B = set(), []
    for w in words(n):
        if w in seen or w == w[::-1]:
            seen.add(w); continue
        seen |= {w, w[::-1]}
        B.append({w: 1, w[::-1]: -1})
    return B

def dimA(n):
    return 2 ** (n - 1) - 2 ** ((n - 1) // 2)

def dimS(n):
    return 2 ** (n - 1) + 2 ** ((n - 1) // 2)

def fmt(p):
    return ' '.join(f'{x:+}{w or "1"}' for w, x in sorted(p.items())) or '0'

# ---------------- subcommands ----------------
def cmd_validate(nmax):
    out('== M vs products of posets (ER Thm 9.2 / Hetyei eq. (5.1)) ==')
    small = [chain(1), chain(2), chain(3), boolean(2), boolean(3), doubled_chain(2, {1}), doubled_chain(3, {2}),
             face_lattice([[i, (i + 1) % 4] for i in range(4)], '4-gon'), random_graded(7, 3, 2)]
    for reading in ('ER', 'PRINTED'):
        bad = tot = 0
        for P in small:
            for Q in small:
                if P.rank + Q.rank > 6:
                    continue
                tot += 1
                lhs = psi(product(P, Q)); rhs = M(psi(P), psi(Q), reading)
                if lhs != rhs:
                    bad += 1
                    if bad <= 3:
                        out(f'  [{reading}] mismatch {P.name} x {Q.name}: Psi(PxQ)={fmt(lhs)}  M={fmt(rhs)}')
        out(f'[{reading}] product pairs tested {tot}, mismatches {bad}')
    out('M(a,1) ER =', fmt(M({'a': 1}, {'': 1}, 'ER')), '| PRINTED =', fmt(M({'a': 1}, {'': 1}, 'PRINTED')),
        '| Psi(chain2 x chain1) =', fmt(psi(product(chain(2), chain(1)))))
    out('== I2 formula (Thm 5.7/32) vs brute-force interval transform of the second kind ==')
    Ps = test_posets()
    for reading in ('ER', 'PRINTED'):
        bad = 0
        for P in Ps:
            bf = interval_transform2_psi(P); fm = I2(psi(P), reading)
            if bf != fm:
                bad += 1
                if bad <= 3:
                    out(f'  [{reading}] mismatch {P.name}: brute={fmt(bf)} formula={fmt(fm)}')
        out(f'[{reading}] posets tested {len(Ps)}: {[P.name for P in Ps] if reading == "ER" else ""} mismatches {bad}')
    out('Psi(P*) == Psi(P)* on all test posets:', all(psi(dual(P)) == star(psi(P)) for P in Ps))
    out('== full pinning: doubled chains D(m,S), all S subset [m], span Q<a,b>_m; brute force vs formula ==')
    for m in range(1, nmax + 1):
        Ds = [doubled_chain(m, set(S)) for k in range(m + 1) for S in itertools.combinations(range(1, m + 1), k)]
        W = words(m)
        rk = rank_exact([[psi(D).get(w, 0) for w in W] for D in Ds])
        res = {}
        for reading in ('ER', 'PRINTED'):
            res[reading] = sum(interval_transform2_psi(D) != I2(psi(D), reading) for D in Ds)
        out(f'degree {m}: {len(Ds)} doubled chains, rank of their ab-indices {rk}/{2**m}; '
            f'mismatches ER {res["ER"]}, PRINTED {res["PRINTED"]}')

def cmd_kernel(n1, n2):
    for n in range(n1, n2 + 1):
        for reading in ('ER', 'PRINTED'):
            A = matrix_of(n, reading)
            rk = rank_exact(A)
            rS = rank_exact(matrix_of(n, reading, sym_basis(n)))
            antiK = all(not I2(p, reading) for p in anti_basis(n))
            out(f'n={n} [{reading}] rank={rk} dimker={2**n - rk} dimA={dimA(n)} dimS={dimS(n)} '
                f'dim(ker cap S)={dimS(n) - rS} A subset ker: {antiK} -> conjecture {"HOLDS" if 2**n - rk == dimA(n) and antiK else "FAILS"}')

U_CERT = {'aaaba': 1, 'aaabb': 1, 'aabaa': -2, 'aabba': -1, 'aabbb': 1, 'abaaa': 1, 'abaab': 1, 'abbaa': -1,
          'abbab': 1, 'abbba': -2, 'baaab': -2, 'baaba': 1, 'baabb': -1, 'babba': 1, 'babbb': 1, 'bbaaa': 1,
          'bbaab': -1, 'bbabb': -2, 'bbbaa': 1, 'bbbab': 1}

def cmd_cert():
    u = U_CERT
    out('u (transcribed from CANDIDATE.md Theorem A):', fmt(u))
    out('terms', len(u), 'degree set', {len(w) for w in u}, 'u* == u:', star(u) == u, 'u != 0:', bool(u))
    for reading in ('ER', 'PRINTED'):
        img = I2(u, reading)
        out(f'[{reading}] I2(u) = {fmt(img)}')
        out(f'[{reading}] coefficient sums of I2(w) over the 20 words:', sorted({sum(dict(I2w(w, reading)).values()) for w in u}))
        out(f'[{reading}] total unit terms sum_w |c_w| * sum|I2(w)| =', sum(abs(c) * sum(abs(x) for x in dict(I2w(w, reading)).values()) for w, c in u.items()))
    # independent: kernel of I2 on S_5 under ER, compare with u
    SB = sym_basis(5)
    rows = matrix_of(5, 'ER', SB)
    ns = nullspace(rows, len(SB))
    out('ER: dim ker(I2|S_5) =', len(ns))
    for vec in ns:
        p = {}
        for c, b in zip(vec, SB):
            p = padd(p, b, c)
        # normalise to integer primitive
        from math import gcd
        dens = 1
        for x in p.values():
            dens = dens * x.denominator // gcd(dens, x.denominator)
        q = {w: int(x * dens) for w, x in p.items()}
        g = 0
        for x in q.values():
            g = gcd(g, abs(x))
        q = {w: x // g for w, x in q.items()}
        out('  kernel generator in S_5:', fmt(q))
        ratio = {Fraction(q.get(w, 0), u[w]) for w in u} | ({0} if set(q) - set(u) else set())
        out('  proportional to lane u:', len(ratio) == 1 and set(q) == set(u), ratio)

def cmd_srcvalues(nmax):
    for reading in ('ER', 'PRINTED'):
        out(f'---- reading {reading} ----')
        # M symmetric (Hetyei eq. Mswap, used in Sec. 6), M(1,1)=c
        asym = [(u, v) for k in range(0, 5) for i in range(k + 1) for u in words(i) for v in words(k - i)
                if dict(Mw(u, v, reading)) != dict(Mw(v, u, reading))]
        out('M(u,v)=M(v,u) for all words, deg u + deg v <= 4: failures', len(asym), asym[:3])
        out('M(1,1) =', fmt(M({'': 1}, {'': 1}, reading)), '(source: c = a+b)')
        # Corollary 5.8/33: I2(u*) = I2(u)
        fails = [w for n in range(1, nmax + 1) for w in words(n) if dict(I2w(w, reading)) != dict(I2w(w[::-1], reading))]
        out(f'Cor 5.8/33 I2(w*)=I2(w), words of length <= {nmax}: failures {len(fails)}', fails[:4])
        # Boolean algebras: I2(Psi(B_k)) = 2^k Psi(B_k)
        for k in range(1, 6):
            pb = psi(boolean(k))
            out(f'B_{k}: I2(Psi) == 2^{k} Psi:', I2(pb, reading) == scal(2 ** k, pb))
        # Prop 5.16 / Thm 5.17 (I2(c^n)): ce- and cd-coefficients, n <= nmax
        okce = okcd = True
        for n in range(1, nmax + 1):
            cn = {'': 1}
            for _ in range(n):
                cn = pmul(cn, {'a': 1, 'b': 1})
            img = I2(cn, reading)
            # predicted ce-expansion: sum over compositions of c^{k0} e^2 c^{k1} ... e^2 c^{kr}, coefficient (-1)^r 2^{n+1-2r}
            pred = {}
            for r in range(0, n // 2 + 1):
                for ks in itertools.product(range(n + 1), repeat=r + 1):
                    if sum(ks) + 2 * r != n:
                        continue
                    poly = {'': 1}
                    for t, kk in enumerate(ks):
                        for _ in range(kk):
                            poly = pmul(poly, {'a': 1, 'b': 1})
                        if t < r:
                            poly = pmul(poly, {'aa': 1, 'ab': -1, 'ba': -1, 'bb': 1})
                    pred = padd(pred, poly, (-1) ** r * 2 ** (n + 1 - 2 * r))
            okce &= (pred == img)
            pred2 = {}
            for r in range(0, n // 2 + 1):
                for ks in itertools.product(range(n + 1), repeat=r + 1):
                    if sum(ks) + 2 * r != n:
                        continue
                    poly = {'': 1}; coef = 2 ** (r + 1)
                    for t, kk in enumerate(ks):
                        coef *= (kk + 1)
                        for _ in range(kk):
                            poly = pmul(poly, {'a': 1, 'b': 1})
                        if t < r:
                            poly = pmul(poly, {'ab': 1, 'ba': 1})
                    pred2 = padd(pred2, poly, coef)
            okcd &= (pred2 == img)
        out(f'Prop 5.16 (ce-coefficients of I2(c^n), with degree n) n<= {nmax}:', okce)
        out(f'Thm 5.17 (cd-coefficients of I2(c^n), with degree n) n<= {nmax}:', okcd)
        # Prop 5.12 consequence: I2(M(u,v)) = M(I2 u, I2 v)
        bad = 0; tot = 0
        for k in range(0, 4):
            for i in range(k + 1):
                for u in words(i):
                    for v in words(k - i):
                        tot += 1
                        if I2(dict(Mw(u, v, reading)), reading) != M(I2({u: 1}, reading), I2({v: 1}, reading), reading):
                            bad += 1
        out(f'I2(M(u,v)) = M(I2 u, I2 v) on word pairs deg<=3 total: {tot} tested, {bad} failures')

def charpoly_rational_roots(rows):
    """eigenvalue candidates: integer divisors are not enough in general, so use exact char poly via
    Faddeev-LeVerrier over Fractions; return (coeffs, rational roots with multiplicity)."""
    n = len(rows)
    A = [[Fraction(x) for x in r] for r in rows]
    Mk = [[Fraction(0)] * n for _ in range(n)]
    c = [Fraction(1)]
    I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{k-1} I
        prev = Mk
        AM = [[sum(A[i][t] * prev[t][j] for t in range(n) if A[i][t] and prev[t][j]) for j in range(n)] for i in range(n)]
        Mk = [[AM[i][j] + c[-1] * I[i][j] for j in range(n)] for i in range(n)]
        AMk = [[sum(A[i][t] * Mk[t][j] for t in range(n) if A[i][t] and Mk[t][j]) for j in range(n)] for i in range(n)]
        tr = sum(AMk[i][i] for i in range(n))
        c.append(-tr / k)
    return c  # char poly x^n + c1 x^{n-1} + ... + cn

def poly_rational_roots(c):
    """roots of monic integer poly x^n + c1 x^{n-1} + ... ; c list of Fractions (should be ints)."""
    coeffs = [int(x) for x in c]
    assert all(Fraction(x) == y for x, y in zip(coeffs, c))
    roots = {}
    p = coeffs[:]
    def ev(p, x):
        r = 0
        for a in p:
            r = r * x + a
        return r
    def div(p, x):
        q, r = [], 0
        for a in p:
            r = r * x + a
            q.append(r)
        return q[:-1]
    while len(p) > 1 and p[-1] == 0:
        roots[0] = roots.get(0, 0) + 1
        p = p[:-1]
    changed = True
    while changed and len(p) > 1:
        changed = False
        cn = abs(p[-1])
        divs = set()
        d = 1
        while d * d <= cn:
            if cn % d == 0:
                divs |= {d, cn // d}
            d += 1
        for d in sorted(divs):
            for x in (d, -d):
                if len(p) > 1 and ev(p, x) == 0:
                    roots[x] = roots.get(x, 0) + 1
                    p = div(p, x)
                    changed = True
                    break
            if changed:
                break
    return roots, len(p) - 1

def Lsrc(p):
    e = {'a': 1, 'b': -1}
    return padd(pmul(e, p), pmul(p, e))

def Ler(p):
    return pmul({'a': 1, 'b': -1}, p)

def is_eig(p, reading):
    """return eigenvalue if p is an eigenvector of I2 (p != 0), else None"""
    if not p:
        return None
    img = I2(p, reading)
    w0 = next(iter(p))
    lam = Fraction(img.get(w0, 0), p[w0])
    return lam if img == {w: lam * x for w, x in p.items() if lam * x != 0} or (lam == 0 and not img) else None

def cmd_eigen(nmax):
    reading = 'ER'
    out('---- 347231 under the ER reading ----')
    for n in range(1, nmax + 1):
        A = matrix_of(n, reading)
        c = charpoly_rational_roots(A)
        roots, rest = poly_rational_roots(c)
        SB = sym_basis(n)
        tot = 0; parts = []
        for lam in sorted(roots):
            rowsS = matrix_of(n, reading, SB)
            W = words(n)
            # (I2 - lam) applied to S-basis
            for j, b in enumerate(SB):
                for w, x in b.items():
                    rowsS[W.index(w)][j] -= lam * x
            d = len(SB) - rank_exact(rowsS)
            Arows = [[A[i][j] - (lam if i == j else 0) for j in range(2 ** n)] for i in range(2 ** n)]
            g = 2 ** n - rank_exact(Arows)
            parts.append(f'{lam}:alg{roots[lam]}/geom{g}/inS{d}')
            tot += d
        out(f'n={n}: eigenvalues {parts}; irrational/non-rational part degree {rest}; '
            f'span of eigenvectors lying in S_n = {tot} of dim S_n = {dimS(n)}')
    # symmetry of image: I2(aab+baa)
    s0 = {'aab': 1, 'baa': 1}
    out('I2(aab) =', fmt(I2({'aab': 1}, reading)))
    out('I2(aab+baa) =', fmt(I2(s0, reading)), '| symmetric?', star(I2(s0, reading)) == I2(s0, reading))
    # Lemma 5.11 / 36
    pb3 = psi(boolean(3))
    out('Psi(B3) =', fmt(pb3), '; eigenvalue', is_eig(pb3, reading))
    out('Lemma 36 check: L(Psi(B3)) =', fmt(Lsrc(pb3)), '; eigenvector?', is_eig(Lsrc(pb3), reading))
    out('I2(L(Psi B3)) - 8 L(Psi B3) =', fmt(padd(I2(Lsrc(pb3), reading), Lsrc(pb3), -8)))
    # Lemma 36 on other Boolean / butterfly eigenvectors
    for k in range(1, 5):
        pb = psi(boolean(k))
        out(f'B_{k}: eig {is_eig(pb, reading)}; L_source(Psi B_{k}) eig {is_eig(Lsrc(pb), reading)}')
    # compositions
    for Lname, Lf in (('L_source=(a-b)u+u(a-b)', Lsrc), ('L_mathdb=(a-b)u', Ler)):
        out(f'-- compositions of Pyr and {Lname} applied to 1 --')
        layer = {(): {'': 1}}
        for n in range(1, nmax + 1):
            new = {}
            for key, p in layer.items():
                new[key + ('P',)] = M({'': 1}, p, reading)
                new[key + ('L',)] = Lf(p)
            layer = new
            W = words(n)
            vecs = [[p.get(w, 0) for w in W] for p in layer.values()]
            rk = rank_exact(vecs)
            noneig = [''.join(k[::-1]) for k, p in layer.items() if is_eig(p, reading) is None]
            nonsym = [''.join(k[::-1]) for k, p in layer.items() if star(p) != p]
            out(f'n={n}: {len(layer)} compositions (outermost first), span dim {rk}, dim S_n {dimS(n)}, '
                f'non-eigenvectors {len(noneig)} e.g. {noneig[:3]}, non-symmetric {len(nonsym)}')

def in_A(p):
    return all(p.get(w[::-1], 0) == -x for w, x in p.items())

def cmd_misc():
    d = {'ab': 1, 'ba': -1}
    for reading in ('ER', 'PRINTED'):
        out(f'[{reading}] I2(ab - ba) =', fmt(I2(d, reading)))
    # robustness of 347231 under a quotient reading (eigenvectors modulo A_n)
    pb3 = psi(boolean(3))
    diff = padd(I2(Lsrc(pb3), 'ER'), Lsrc(pb3), -8)
    out('L(Psi B3): I2(L) - 8 L in A_3 (eigenvector modulo A)?', in_A(diff), '| diff =', fmt(diff))
    for lam in (0, 2, 4, 8, 16):
        out(f'  I2(L) - {lam} L in A_3?', in_A(padd(I2(Lsrc(pb3), 'ER'), Lsrc(pb3), -lam)))
    # Theorem B argument re-derived: I2 maps S_n into S_n?
    for n in range(1, 6):
        bad = [fmt(b) for b in sym_basis(n) if star(I2(b, 'ER')) != I2(b, 'ER')]
        out(f'n={n}: symmetric basis elements with non-symmetric I2-image: {len(bad)} {bad[:3]}')

def main():
    global LOG
    logp = sys.argv[1]
    if os.path.exists(logp):
        sys.exit('refusing to overwrite log ' + logp)
    os.makedirs(os.path.dirname(os.path.abspath(logp)), exist_ok=True)
    LOG = open(logp, 'x')
    out('argv:', ' '.join(sys.argv[1:]))
    cmd = sys.argv[2]
    if cmd == 'validate':
        cmd_validate(int(sys.argv[3]))
    elif cmd == 'kernel':
        cmd_kernel(int(sys.argv[3]), int(sys.argv[4]))
    elif cmd == 'cert':
        cmd_cert()
    elif cmd == 'srcvalues':
        cmd_srcvalues(int(sys.argv[3]))
    elif cmd == 'eigen':
        cmd_eigen(int(sys.argv[3]))
    elif cmd == 'misc':
        cmd_misc()
    out('done')

main()

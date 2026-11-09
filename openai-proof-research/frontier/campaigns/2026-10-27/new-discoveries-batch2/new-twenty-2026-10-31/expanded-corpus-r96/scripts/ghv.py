r"""376197: GHV upper bound rho^(I_Delta(M)) <= omega / alpha^(I_Delta(M)) for matroids (arXiv:2607.20892, Conj. 8.4).

Formulas used (all from the source):
  * I_Delta(M) = (x^C : C circuit of M); omega = max circuit size of M.
  * I_Delta(M) = cap_{B basis} P_{E\B}, so alpha^(I_Delta(M)) = min sum a_i s.t. a(E\B) >= 1 for all bases B, a >= 0.
  * Lemma (line 820): rho^(I_Delta(M)) = rho^(I(M*)), I(N) the facet (basis) ideal.
  * Theorem 3.9: rho^(I(N)) = max_{F flat of N, F != E} (rk N - rk_N F) / alpha^(I(N/F)).
  * Line 854: SP(I(N)) = { a >= 0 : a(C) >= 1 for every circuit C of N* }, so alpha^(I(N)) is the
    fractional transversal number of the circuits of N*.  With N = M*, N/F = M*/F and (M*/F)* = M \ F,
    so alpha^(I(M*/F)) = min a(E\F) s.t. a(C) >= 1 for every circuit C of M with C subset E\F.
LPs are solved with scipy HiGHS (floating point) for screening; any violation must be re-certified exactly.
usage: ghv.py random q kmax nmax trials seed
"""
import sys, json, itertools, random, resource
import numpy as np
from scipy.optimize import linprog
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))

def rank_gf(rows, q):
    M = [list(r) for r in rows]; r = 0
    if not M: return 0
    ncol = len(M[0])
    for c in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]; inv = pow(M[r][c], q - 2, q)
        M[r] = [(x * inv) % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % q:
                f = M[i][c]; M[i] = [(x - f * y) % q for x, y in zip(M[i], M[r])]
        r += 1
    return r

def matroid_from_matrix(A, q):
    k = len(A); n = len(A[0]); cols = [[A[i][j] for i in range(k)] for j in range(n)]
    rk = {}
    for S in range(1 << n):
        rk[S] = rank_gf([cols[j] for j in range(n) if S >> j & 1], q)
    return n, rk

def analyze(n, rk):
    full = (1 << n) - 1; k = rk[full]
    bases = [S for S in range(1 << n) if bin(S).count('1') == k and rk[S] == k]
    dep = lambda S: rk[S] < bin(S).count('1')
    circuits = [S for S in range(1, 1 << n) if dep(S) and all(not dep(S & ~(1 << i)) for i in range(n) if S >> i & 1)]
    if not circuits: return None
    omega = max(bin(C).count('1') for C in circuits)
    # alpha^(I_Delta(M))
    A = [[-1.0 if not (B >> i & 1) else 0.0 for i in range(n)] for B in bases]
    res = linprog(np.ones(n), A_ub=np.array(A), b_ub=-np.ones(len(bases)), bounds=[(0, None)] * n, method='highs')
    alpha_hat = res.fun
    # dual matroid rank: rk*(S) = |S| - k + rk(E\S)
    rkd = lambda S: bin(S).count('1') - k + rk[full & ~S]
    kd = n - k
    # flats of M*: S with rk*(S + e) > rk*(S) for all e not in S
    best = 0.0; arg = None
    for F in range(1 << n):
        if F == full: continue
        r = rkd(F)
        if any(not (F >> e & 1) and rkd(F | 1 << e) == r for e in range(n)): continue
        comp = full & ~F
        cs = [C for C in circuits if C & F == 0]
        if not cs: continue
        idx = [i for i in range(n) if comp >> i & 1]
        Aub = [[-1.0 if C >> i & 1 else 0.0 for i in idx] for C in cs]
        res = linprog(np.ones(len(idx)), A_ub=np.array(Aub), b_ub=-np.ones(len(cs)), bounds=[(0, None)] * len(idx), method='highs')
        val = (kd - r) / res.fun
        if val > best + 1e-12: best, arg = val, F
    return {'n': n, 'k': k, 'omega': omega, 'alpha_hat': alpha_hat, 'rho_hat': best, 'argflat_Mstar': arg,
            'bound': omega / alpha_hat, 'slack': omega / alpha_hat - best}

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'uniform':  # sanity: rho^ = (k+1)(n-k)/n = omega/alpha^
        for n in range(2, 8):
            for k in range(1, n):
                rk = {S: min(bin(S).count('1'), k) for S in range(1 << n)}
                r = analyze(n, rk); print(json.dumps({**r, 'expected_rho': (k + 1) * (n - k) / n}))
    elif mode == 'random':
        q, kmax, nmax, trials, seed = map(int, sys.argv[2:7]); rnd = random.Random(seed)
        seen = set(); worst = None; viol = []
        for t in range(trials):
            n = rnd.randint(3, nmax); k = rnd.randint(1, min(kmax, n - 1))
            # columns: mix of random, zero (loops) and repeated (parallel) columns
            cols = []
            for j in range(n):
                u = rnd.random()
                if j > 0 and u < 0.2: cols.append(list(cols[rnd.randrange(j)]))
                elif u < 0.23: cols.append([0] * k)
                else: cols.append([rnd.randrange(q) for _ in range(k)])
            A = [[cols[j][i] for j in range(n)] for i in range(k)]
            n_, rk = matroid_from_matrix(A, q)
            if rk[(1 << n) - 1] != k: continue
            key = tuple(sorted(S for S in range(1 << n) if rk[S] == k and bin(S).count('1') == k))
            if (n, key) in seen: continue
            seen.add((n, key)); r = analyze(n, rk)
            if r is None: continue
            if worst is None or r['slack'] < worst['slack']: worst = {**r, 'matrix': A}
            if r['slack'] < -1e-9: viol.append({**r, 'matrix': A})
        print(json.dumps({'q': q, 'trials': trials, 'distinct_labeled': len(seen), 'violations': viol[:5], 'n_viol': len(viol), 'min_slack': worst}))

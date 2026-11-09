"""s4: Lemma A (last-vertex neighbourhood) re-checked three ways:
  (i)   integer Lagrange inversion identity n [z^n] f^j = j [w^{n-j}] A^n on random integer A (exact ints);
  (ii)  Lemma A against the recurrence construction on random Bell-type A (NOT only io), N = 4..128;
  (iii) the reverse-relabelling route: CJKM v2 Thm 3.14 / Jung Lemma 2.3, G^r_n = G_n((zA)' A^{n-2}, z/A),
        checked against the literal label reversal, and its vertex-1 column compared with Lemma A."""
import sys, random
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

rng = random.Random(337352)

# (i) integer Lagrange inversion
def zmul(x, y, t):
    r = [0] * t
    for i, xi in enumerate(x[:t]):
        if xi:
            for j, yj in enumerate(y[: t - i]):
                r[i + j] += xi * yj
    return r

def zpow(x, e, t):
    r = [1] + [0] * (t - 1)
    for _ in range(e):
        r = zmul(r, x, t)
    return r

def zsolve_f(A, t):
    f = [0] * t
    for _ in range(t + 1):
        # f = z * A(f)
        acc = [0] * t
        p = [1] + [0] * (t - 1)
        for i in range(t):
            if i < len(A) and A[i]:
                acc = [u + A[i] * v for u, v in zip(acc, p)]
            p = zmul(p, f, t)
        nf = [0] + acc[: t - 1]
        if nf == f:
            break
        f = nf
    return f

bad = 0; tot = 0
for trial in range(40):
    t = 11
    A = [rng.choice([1, -1, 2])] + [rng.randrange(-2, 3) for _ in range(t - 1)]
    A[0] = 1  # a_0 = 1 (proper); also tests 0/1 and signed lifts
    f = zsolve_f(A, t)
    for n in range(1, t):
        An = zpow(A, n, t)
        for j in range(1, n + 1):
            fj = zpow(f, j, t)
            tot += 1
            if n * fj[n] != j * An[n - j]:
                bad += 1
print('(i) integer Lagrange identity n[z^n]f^j = j[w^(n-j)]A^n: checked', tot, 'failures', bad)

# (ii) Lemma A against the recurrence (random Bell-type A, arbitrary a_1, ...)
bad = 0; tot = 0
for K in range(2, 8):
    N = 2 ** K
    for trial in range(150 if K < 7 else 40):
        a = [1] + [rng.randrange(2) for _ in range(N - 2)]
        if trial % 3 == 0:
            a = random_io(N - 1, rng)
        G = riordan_graph(a, N)
        inv = ps_inv(amask(a), N)
        pred = 0
        for j in range(1, N):
            if j % 2 == 1 and (inv >> (N - 1 - j)) & 1:
                pred |= 1 << (j - 1)
        tot += 1
        if G[N - 1] != pred:
            bad += 1
print('(ii) Lemma A vs recurrence, N = 4..128: checked', tot, 'graphs, failures', bad)

# (iii) Jung Lemma 2.3 / CJKM Thm 3.14 against literal reversal, and its first column
def deriv(x):
    r = 0
    i = 1
    while (x >> i):
        if (x >> i) & 1 and i % 2 == 1:
            r |= 1 << (i - 1)
        i += 1
    return r

def gpow(x, e, t):
    r = 1
    for _ in range(e):
        r = clmul(r, x, t)
    return r

bad_rev = 0; bad_col = 0; tot = 0
for n in (5, 6, 8, 9, 12, 16, 17, 32):
    for trial in range(40):
        a = [1] + [rng.randrange(2) for _ in range(n - 2)]
        A = amask(a)
        t = n + 2
        G = riordan_graph(a, n)
        rev = [0] * n
        for v in range(n):
            for u in range(n):
                if (G[v] >> u) & 1:
                    rev[n - 1 - v] |= 1 << (n - 1 - u)
        zA = A << 1
        gr = clmul(deriv(zA), gpow(A, n - 2, t), t)
        fr = clmul(1 << 1, ps_inv(A, t), t)  # z / A
        Gr = riordan_graph_general(gr, fr, n)
        tot += 1
        if Gr != rev:
            bad_rev += 1
        # vertex 1 of G^r is vertex n of G: neighbours i of 1 in G^r <-> j = n+1-i in G
        if n & (n - 1) == 0:
            inv = ps_inv(A, n)
            pred = 0
            for j in range(1, n):
                if j % 2 == 1 and (inv >> (n - 1 - j)) & 1:
                    pred |= 1 << (j - 1)
            col = 0
            for i in range(2, n + 1):
                if (gr >> (i - 2)) & 1:
                    col |= 1 << (n + 1 - i - 1)
            if col != pred:
                bad_col += 1
print('(iii) Thm 3.14 / Lemma 2.3 vs literal reversal: checked', tot, 'graphs, failures', bad_rev,
      '; first-column-of-reversal vs Lemma A formula (n power of 2) failures', bad_col)

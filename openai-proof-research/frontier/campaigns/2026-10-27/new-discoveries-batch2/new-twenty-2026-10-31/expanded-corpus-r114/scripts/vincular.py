# Conjecture A.2 of arXiv:2508.13709 (MathDB 369839): (P_n^{(1)}(x)) and (P_n^{(2)}(x)) are Stieltjes moment
# sequences for every x >= 0, where P_n^{(c)}(x) = sum over permutations of [n] of x^{#occurrences}, Class 1
# represented by the vincular pattern 1-23 and Class 2 by 1-32 (classes are equidistributed, Prop. A.1).
# Exact DP over (length j, rank a of last entry among the first j entries):
#   append entry of rank b in 1..j+1 among the first j+1 entries.
#   1-23: occurrence (i, j, j+1) needs sigma_i < sigma_j < sigma_{j+1}; new occurrences = [b > a] * (a - 1).
#   1-32: occurrence (i, j, j+1) needs sigma_i < sigma_{j+1} < sigma_j; new occurrences = [b <= a] * (b - 1).
# S-fraction coefficients alpha_k of sum a_n t^n = a_0/(1 - alpha_1 t/(1 - alpha_2 t/(1 - ...))) via the
# quotient-difference (Stieltjes) recursion in exact rationals at rational x.
import sys, json, itertools
from fractions import Fraction as F

def poly_counts(N, cls, x):
    out = [F(1), F(1)]  # n = 0, 1
    dp = {1: F(1)}      # j = 1
    for j in range(1, N):
        nd = {}
        for a, w in dp.items():
            for b in range(1, j + 2):
                if cls == 1: e = (a - 1) if b > a else 0
                else: e = (b - 1) if b <= a else 0
                nd[b] = nd.get(b, 0) + w * x ** e
        dp = nd; out.append(sum(dp.values()))
    return out

def brute(n, cls):
    from collections import Counter
    C = Counter()
    for s in itertools.permutations(range(n)):
        occ = 0
        for j in range(n - 1):
            for i in range(j):
                if cls == 1 and s[i] < s[j] < s[j + 1]: occ += 1
                if cls == 2 and s[i] < s[j + 1] < s[j]: occ += 1
        C[occ] += 1
    return C

def sfraction(a, K):
    # Continued fraction via the "Stieltjes table": f0(t) = sum a_n t^n / a_0; f_{k-1}(t) = 1/(1 - alpha_k t f_k(t)).
    f = [c / a[0] for c in a]; alphas = []
    for k in range(K):
        if len(f) < 2: break
        alpha = f[1]; alphas.append(alpha)
        if alpha == 0: break
        # f = 1/(1 - alpha t g) => g = (1 - 1/f)/(alpha t); compute 1/f as power series
        L = len(f); inv = [F(0)] * L; inv[0] = 1 / f[0]
        for n in range(1, L): inv[n] = -sum(f[i] * inv[n - i] for i in range(1, n + 1)) / f[0]
        g = [-inv[n + 1] / alpha for n in range(L - 1)]
        f = g
    return alphas

if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        for cls in (1, 2):
            for n in range(1, 8):
                C = brute(n, cls); xs = F(3, 2)
                assert sum(v * xs ** k for k, v in C.items()) == poly_counts(n, cls, xs)[n], (cls, n)
        assert poly_counts(8, 1, F(0)) == [1, 1, 2, 5, 15, 52, 203, 877, 4140]  # Bell numbers (Claesson)
        print('selftest ok'); sys.exit()
    N = int(sys.argv[1]); xs = [F(s) for s in sys.argv[2].split(',')]; res = []
    for cls in (1, 2):
        for x in xs:
            a = poly_counts(N, cls, x); al = sfraction(a, N)
            neg = [i + 1 for i, v in enumerate(al) if v < 0]
            res.append(dict(cls=cls, x=str(x), terms=len(a), coefficients=len(al), first_negative=neg[:5],
                            min_alpha=float(min(al)), min_index=int(min(range(len(al)), key=lambda i: al[i])) + 1))
            print(cls, x, len(al), 'neg', neg[:5], 'min', float(min(al)), flush=True)
    json.dump(res, open(sys.argv[3], 'w'), indent=1)

def qd_alphas(a, prec=3000):
    # Quotient-difference algorithm: alpha_{2k-1} = q_k^{(0)}, alpha_{2k} = e_k^{(0)} (Rutishauser), in Decimal.
    import decimal
    ctx = decimal.Context(prec=prec); D = lambda v: ctx.divide(decimal.Decimal(v.numerator), decimal.Decimal(v.denominator))
    a = [D(v) for v in a]; N = len(a)
    q = [ctx.divide(a[n + 1], a[n]) for n in range(N - 1)]; e = [decimal.Decimal(0)] * N
    al = []
    for k in range(1, N):
        if len(q) < 1: break
        al.append(q[0])
        e = [ctx.add(ctx.subtract(q[n + 1], q[n]), e[n + 1]) for n in range(len(q) - 1)]
        if not e: break
        al.append(e[0])
        if any(v == 0 for v in e[:-1]): break
        q = [ctx.divide(ctx.multiply(q[n + 1], e[n + 1]), e[n]) for n in range(len(e) - 1)]
    return al

def run_qd(N, xs, path):
    res = []
    for cls in (1, 2):
        for x in xs:
            al = qd_alphas(poly_counts(N, cls, x)); neg = [i + 1 for i, v in enumerate(al) if v < 0]
            res.append(dict(cls=cls, x=str(x), terms=N + 1, coefficients=len(al), first_negative=neg[:5],
                            min_alpha=float(min(al)), min_index=int(min(range(len(al)), key=lambda i: al[i])) + 1,
                            first_alphas=[float(v) for v in al[:8]]))
            print(cls, x, len(al), 'neg', neg[:5], 'min %.4g at %d' % (float(min(al)), res[-1]['min_index']), flush=True)
    json.dump(res, open(path, 'w'), indent=1)

def run_qd_decimal(N, xstr, path, prec=2500):
    # Same DP and qd in Decimal arithmetic (DP adds positive terms only; qd checked against exact for small N).
    import decimal
    decimal.getcontext().prec = prec
    res = []
    for cls in (1, 2):
        x = decimal.Decimal(F(xstr).numerator) / decimal.Decimal(F(xstr).denominator)
        pw = [decimal.Decimal(1)]
        for _ in range(N): pw.append(pw[-1] * x)
        out = [decimal.Decimal(1), decimal.Decimal(1)]; dp = {1: decimal.Decimal(1)}
        for j in range(1, N):
            nd = [decimal.Decimal(0)] * (j + 2)
            for a, w in dp.items():
                for b in range(1, j + 2):
                    e = ((a - 1) if b > a else 0) if cls == 1 else ((b - 1) if b <= a else 0)
                    nd[b] += w * pw[e]
            dp = {b: nd[b] for b in range(1, j + 2)}; out.append(sum(dp.values()))
        a = out; Nn = len(a); ctx = decimal.getcontext()
        q = [a[n + 1] / a[n] for n in range(Nn - 1)]; e = [decimal.Decimal(0)] * Nn; al = []
        while q:
            al.append(q[0]); e = [q[n + 1] - q[n] + e[n + 1] for n in range(len(q) - 1)]
            if not e: break
            al.append(e[0])
            if any(v == 0 for v in e[:-1]): break
            q = [q[n + 1] * e[n + 1] / e[n] for n in range(len(e) - 1)]
        neg = [i + 1 for i, v in enumerate(al) if v < 0]
        res.append(dict(cls=cls, x=xstr, terms=N + 1, coefficients=len(al), first_negative=neg[:5], min_alpha=float(min(al)),
                        min_index=int(min(range(len(al)), key=lambda i: al[i])) + 1, alphas_head=[float(v) for v in al[:6]], alphas_tail=[float(v) for v in al[-4:]]))
        print(cls, xstr, len(al), 'neg', neg[:5], 'min %.4g at %d' % (res[-1]['min_alpha'], res[-1]['min_index']), 'tail', [round(float(v), 3) for v in al[-4:]], flush=True)
    json.dump(res, open(path, 'w'), indent=1)

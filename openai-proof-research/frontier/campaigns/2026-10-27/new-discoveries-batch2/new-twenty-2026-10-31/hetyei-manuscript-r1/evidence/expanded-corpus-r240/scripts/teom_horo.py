"""346858 exploration: horocyclic finite-type settings on T_2 (3-regular tree with a fixed end).
tEoM on edge <ij>:  (1/P_ij)(c_i^2/d_i^2 + c_j^2/d_j^2) - c_i/d_i - c_j/d_j = 0,
c_i = sum_{e at i} 1/P_e, d_i = sum 1/P_e^2  (Huang-Stoica-Xia-Zhong arXiv:2006.06716, (3.1), (5.1)).
Ansatz: vertex of type T with parent-edge length s has child edges s*x_T (child type sig_T) and
s*y_T (child type tau_T). Then c/d = s*A_T, A_T = (1+1/x+1/y)/(1+1/x^2+1/y^2), and the tEoM on the
x-edge reads  A_T^2 + x^2 A_U^2 = x (A_T + x A_U)  (U = child type), similarly for y.
Random-start damped Newton over log-variables; reports positive solutions that are not constant.
Usage: teom_horo.py K NSTARTS SEED"""
import sys, itertools, random, math
K, NS, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
random.seed(SEED)
def A(x, y): return (1 + 1 / x + 1 / y) / (1 + 1 / x ** 2 + 1 / y ** 2)
def F(z, sig, tau):
    X = [math.exp(t) for t in z]
    xs, ys = X[0::2], X[1::2]
    As = [A(xs[t], ys[t]) for t in range(K)]
    out = []
    for t in range(K):
        for v, U in ((xs[t], sig[t]), (ys[t], tau[t])):
            out.append((As[t] ** 2 + v * v * As[U] ** 2 - v * (As[t] + v * As[U])) / (As[t] ** 2 + v * v * As[U] ** 2))
    return out
def solve(lin, z):
    n = len(z); M = [row[:] + [b] for row, b in zip(lin[0], lin[1])]
    for c in range(n):
        p = max(range(c, n), key=lambda i: abs(M[i][c]))
        if abs(M[p][c]) < 1e-14: return None
        M[c], M[p] = M[p], M[c]
        for i in range(n):
            if i != c:
                f = M[i][c] / M[c][c]; M[i] = [a - f * b for a, b in zip(M[i], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
found = []
for sig in itertools.product(range(K), repeat=K):
    for tau in itertools.product(range(K), repeat=K):
        if any(sig[t] > tau[t] for t in range(K)): continue  # x/y symmetry within a type
        for _ in range(NS):
            z = [random.uniform(-2.5, 2.5) for _ in range(2 * K)]
            ok = False
            for it in range(80):
                f = F(z, sig, tau); nf = math.sqrt(sum(v * v for v in f))
                if nf < 1e-13: ok = True; break
                J = []
                for j in range(2 * K):
                    zz = z[:]; zz[j] += 1e-7; fj = F(zz, sig, tau)
                    J.append([(a - b) / 1e-7 for a, b in zip(fj, f)])
                Jt = [[J[j][i] for j in range(2 * K)] for i in range(2 * K)]
                d = solve((Jt, [-v for v in f]), z)
                if d is None: break
                lam = 1.0
                while lam > 1e-4:
                    zn = [a + lam * b for a, b in zip(z, d)]
                    if all(abs(t) < 30 for t in zn):
                        fn = F(zn, sig, tau)
                        if math.sqrt(sum(v * v for v in fn)) < nf: z = zn; break
                    lam /= 2
                else:
                    break
            if ok:
                X = [math.exp(t) for t in z]
                if max(abs(v - 1) for v in X) > 1e-6:
                    key = (sig, tau, tuple(round(v, 6) for v in X))
                    if key not in found:
                        found.append(key); print('NONCONSTANT', sig, tau, [round(v, 10) for v in X], flush=True)
print('K', K, 'nonconstant positive solutions found', len(found))

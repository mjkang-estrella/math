#!/usr/bin/env python3
"""MIT. Independent reviewer finite diagnostics for T117Q. Not a proof and not a
proof dependency: finite floating-point checks of algebraic steps only."""
import itertools, json, math, sys
import numpy as np
from numpy.polynomial.hermite_e import hermegauss

rng = np.random.default_rng(20261018)
TOL = 1e-9


def opnorm(a):
    return float(np.linalg.norm(a, 2))


def hsym(a):
    return (a + a.conj().T) / 2


def psd_power(a, t):
    w, v = np.linalg.eigh(hsym(a))
    return (v * np.clip(w, 0, None) ** t) @ v.conj().T


def random_tuple(m, d):
    xs = [hsym(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) for _ in range(m)]
    c = math.sqrt(opnorm(sum(x @ x for x in xs)))
    return [x / c for x in xs]


PAULI = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]),
         np.array([[1, 0], [0, -1]], complex)]


def pairings(n):
    """All perfect matchings of range(n), as lists of (a,b) with a<b."""
    def rec(rest):
        if not rest:
            yield []
            return
        a = rest[0]
        for k in range(1, len(rest)):
            for tail in rec(rest[1:k] + rest[k + 1:]):
                yield [(a, rest[k])] + tail
    return list(rec(list(range(n))))


def crossing(p):
    return any(a < c < b < e for (a, b) in p for (c, e) in p)


def word_sum(xs, p, n):
    m, d = len(xs), xs[0].shape[0]
    total = np.zeros((d, d), complex)
    for labels in itertools.product(range(m), repeat=len(p)):
        w = [0] * n
        for lab, (a, b) in zip(labels, p):
            w[a] = w[b] = lab
        prod = np.eye(d, dtype=complex)
        for j in w:
            prod = prod @ xs[j]
        total += prod
    return total


def product_rule(m, k):
    nodes, weights = hermegauss(k)
    weights = weights / weights.sum()
    for idx in itertools.product(range(k), repeat=m):
        yield np.array([nodes[i] for i in idx]), float(np.prod([weights[i] for i in idx]))


out = {}

# A. Lemma 1: every pairing (crossing and nested) word sum has norm <= 1;
#    the full sum matches Gaussian quadrature, is PSD and <= (2q-1)!! I.
worst_word, crossing_seen, crossing_nonpsd, cases = 0.0, 0, 0, 0
for name, xs in [('pauli/sqrt3', [p / math.sqrt(3) for p in PAULI]),
                 ('rand m3 d4', random_tuple(3, 4)), ('rand m2 d5', random_tuple(2, 5))]:
    m, d = len(xs), xs[0].shape[0]
    for q in (1, 2, 3):
        n = 2 * q
        tot = np.zeros((d, d), complex)
        for p in pairings(n):
            ws = word_sum(xs, p, n)
            worst_word = max(worst_word, opnorm(ws))
            assert opnorm(ws) <= 1 + TOL, (name, q, p)
            if crossing(p):
                crossing_seen += 1
                if np.linalg.eigvalsh(hsym(ws))[0] < -1e-6 or opnorm(ws - ws.conj().T) > 1e-6:
                    crossing_nonpsd += 1
            tot += ws
        quad = sum(w * np.linalg.matrix_power(sum(g[j] * xs[j] for j in range(m)), n)
                   for g, w in product_rule(m, q + 1))
        assert opnorm(tot - quad) < 1e-8
        ev = np.linalg.eigvalsh(hsym(tot))
        dfact = math.prod(range(1, n, 2))
        assert ev[0] > -TOL and ev[-1] <= dfact + TOL
        cases += 1
out['lemma1'] = {'tuple_moment_cases': cases, 'max_pairing_word_norm': worst_word,
                 'crossing_pairing_sums_checked': crossing_seen,
                 'crossing_sums_not_psd': crossing_nonpsd}
# Negative control: a trace-normalized variance condition is not the operator one.
X = np.diag([1.25, 0.0])
assert np.trace(X @ X).real / 2 <= 1 and opnorm(X @ X) > 1  # E(gX)^2 = X^2 not <= I
out['lemma1']['trace_normalized_variance_control'] = 'E(gX)^2=diag(1.5625,0) violates <=I although tr(X^2)/2<1'

# B. Lemma 2 chain under a finite law with exact Gaussian moments to degree 11.
m, d, S, N, q = 3, 6, 9, 5, 2
A = [hsym(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) for _ in range(m)]
Xs = [np.zeros((d, d), complex) for _ in range(m)]
Y_abs, e_tr = np.zeros((d, d), complex), 0.0
for g, w in product_rule(m, 6):
    ev, ve = np.linalg.eigh(sum(g[j] * A[j] for j in range(m)))
    sg = (ve * np.sign(ev)) @ ve.conj().T
    for j in range(m):
        Xs[j] += w * g[j] * sg
    Y_abs += w * (ve * np.abs(ev)) @ ve.conj().T
    e_tr += w * float(np.abs(ev).sum())
Y = sum(A[j] @ Xs[j] for j in range(m))
assert opnorm(Y - Y_abs) < 1e-10 and np.linalg.eigvalsh(hsym(Y))[0] > -TOL
assert abs(np.trace(Y).real - e_tr) < 1e-9
assert np.linalg.eigvalsh(hsym(sum(x @ x for x in Xs)))[-1] <= 1 + TOL
u = rng.normal(size=(S, N, m)) / math.sqrt(m)
u[0] *= 6.0  # one badly aligned chart, which the selector must tolerate
pert = 1e-3
results = []
for mismatch in (0.0, pert):
    Z = [[sum(u[s, i, j] * Xs[j] for j in range(m)) for i in range(N)] for s in range(S)]
    Qs = [psd_power(sum(np.linalg.matrix_power(z, 2 * q) for z in Z[s]), 1 / q) for s in range(S)]
    h = 2 * float(np.linalg.eigvalsh(hsym(sum(Qs) / S))[-1])
    P = []
    for Qm in Qs:
        ev, ve = np.linalg.eigh(hsym(Qm))
        P.append((ve * (ev <= h)) @ ve.conj().T)
    slack = float(np.linalg.eigvalsh(hsym(sum(P)) - S / 2 * np.eye(d))[0])
    assert slack >= -TOL
    lhs = S / 2 * np.trace(Y).real
    mid = sum(np.trace(Y @ Pm) for Pm in P)
    assert abs(mid.imag) < 1e-9 and lhs <= mid.real + 1e-8
    t, e, neg_terms, rhs_terms = 0.0, 0.0, 0, 0j
    for s in range(S):
        As = [A[j] + mismatch * hsym(rng.normal(size=(d, d))) for j in range(m)]
        pinv = np.linalg.pinv(u[s])  # m x N, pinv @ u[s] = I_m
        b = [sum(pinv[j, i] * As[j] for j in range(m)) for i in range(N)]
        # Non-minimal coefficients: add components annihilated by u[s]^T, so the
        # representation still holds exactly while individual summands lose sign.
        Cn = (np.eye(N) - u[s] @ pinv) @ rng.normal(size=(N, 2))
        W = [hsym(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) for _ in range(2)]
        b = [b[i] + sum(Cn[i, k] * W[k] for k in range(2)) for i in range(N)]
        for j in range(m):
            assert opnorm(sum(u[s, i, j] * b[i] for i in range(N)) - As[j]) < 1e-9
        t = max(t, max(float(np.linalg.svd(bi, compute_uv=False).sum()) for bi in b))
        e = max(e, sum(float(np.linalg.svd(A[j] - As[j], compute_uv=False).sum()) for j in range(m)))
        for i in range(N):
            assert opnorm(Z[s][i] @ P[s]) ** 2 <= h + 1e-9
            term = np.trace(b[i] @ Z[s][i] @ P[s])
            neg_terms += int(term.real < 0 or abs(term.imag) > 1e-9)
            rhs_terms += term
        for j in range(m):
            rhs_terms += np.trace((A[j] - As[j]) @ Xs[j] @ P[s])
    assert abs(rhs_terms - mid) < 1e-8
    assert mid.real <= S * N * t * math.sqrt(h) + S * e + 1e-8
    results.append({'mismatch_scale': mismatch, 'selector_sum_slack': slack,
                    'trace_Y': float(np.trace(Y).real),
                    'bound_2Nt_sqrt_h_plus_2e': 2 * N * t * math.sqrt(h) + 2 * e,
                    'individual_terms_nonreal_or_negative': neg_terms,
                    'projector_ranks': [int(round(np.trace(Pm).real)) for Pm in P]})
out['lemma2'] = results

# C. Banach-valued (trace-norm) cube inequality (5.4) with constant sqrt(pi/2).
m, d, K, n = 3, 3, 4, 40000
om = rng.normal(size=(K, m)) * 1.5
M = [hsym(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) for _ in range(K)]
def trnorm(a):
    return float(np.abs(np.linalg.eigvalsh(a)).sum())
def hval(th):
    return sum(math.sin(float(om[k] @ th)) * M[k] for k in range(K))
def grad(th):
    return [sum(math.cos(float(om[k] @ th)) * om[k, j] * M[k] for k in range(K)) for j in range(m)]
th = rng.uniform(-1, 1, size=(n, m)); et = rng.uniform(-1, 1, size=(n, m)); gg = rng.normal(size=(n, m))
lhs = np.mean([trnorm(hval(a) - hval(b)) for a, b in zip(th, et)])
rhs = np.mean([trnorm(sum(g[j] * D[j] for j in range(m))) for g, D in ((g, grad(a)) for g, a in zip(gg, th))])
assert lhs <= math.sqrt(math.pi / 2) * rhs
out['cube_inequality'] = {'samples': n, 'lhs': float(lhs), 'sqrt(pi/2)*rhs': float(math.sqrt(math.pi / 2) * rhs)}

# D. Exact exponent bookkeeping in log(m) units (identities and explicit inequalities).
rows = []
for k in (10, 20, 40, 80):
    m = 2 ** k; L = math.log(m); q = math.ceil(6 * L); logS = 10 * q * L; logN = 6 * L
    logeps = -200 * L - logS
    assert abs((logeps + logS + logN) - (-194 * L)) < 1e-6           # epsilon*S*N = m^-194
    assert logN / q <= 1 + 1e-12                                       # N^(1/q) <= e
    hoeff = (2 * q + 6) * L - q * math.log(16)                         # log(R u^2/B^2)
    assert hoeff - math.log(2 * q * L) > 10                            # exp(-hoeff) beats m^(2q) words
    dfact = sum(math.log(2 * i - 1) for i in range(1, q + 1))
    a1, a2 = dfact - q * L, math.log(2) - 2 * q * L
    hi = max(a1, a2)
    assert hi + math.log(math.exp(a1 - hi) + math.exp(a2 - hi)) <= q * (math.log(4 * q) - L)
    logtau = -2000 * L - 2 * logS
    assert logS + 610 * L + logtau < -8 * L - math.log(10)             # S m^610 tau <= r/10
    x = math.log(8) + 0.5 * L - logtau                                 # log(8 sqrt(m)/tau) > 0
    logH0 = logN + x + math.log1p(math.exp(-x))
    rows.append({'log2_m': k, 'q': q, 'logS_over_logm_sq': logS / L ** 2,
                 'log_r_over_delta_over_logm_sq': (1997 * L + 2 * logS) / L ** 2,
                 'logH0_over_logm_sq': logH0 / L ** 2,
                 'hoeffding_log_exponent': hoeff})
out['exponents'] = rows
out['environment'] = {'python': sys.version.split()[0], 'numpy': np.__version__, 'seed': 20261018}
out['status'] = 'PASS'
out['scope'] = ('Finite floating-point and exponent-arithmetic diagnostics only. They do not '
                'establish the arbitrary-dimension, all-size theorem and are not proof dependencies.')
print(json.dumps(out, indent=2))

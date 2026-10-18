#!/usr/bin/env python3
"""Exact rational checks of the inner-leg entry-adjoint formulas (candidate Sec. 3).

Independent proof-review code, t298p-proof-r2. Not derived from author or r1 code.

Model: u, t free standard semicirculars (u differentiated, t a coefficient
variable). Then xi_u = u is the conjugate variable of u relative to t.
Moments are computed EXACTLY by counting colour-respecting noncrossing
pairings. Checks, for random integer polynomials q, x, y:

 (A) scalar inner-leg identity
     (tau x tau)( d_u q # (x (x) y) ) = tau( Xi q ),
     Xi = y u x - y (tau(x)1) d_u x - ((1(x)tau) d_u y) x,
     where # inserts x on the right of the first leg and y on the left of
     the second leg;
 (B) the matrix-unit contraction: for the derivation Delta_bc[x(x)y] on
     M_k(C<u,t>) vanishing on M_k and t, with Delta(u)=sum_i (E_ib x)(x)(E_ci y),
     (tr_k(x)tau)^{(x)2}(Delta(p)) = (1/k)(tr_k(x)tau)((E_cb (x) Xi) p);
 (C) the Leibniz rule and M_k-centrality of the inserted value.
These are finite algebraic identities. They do not prove existence of
conjugate variables, convergence of series or any entropy statement.
"""
import json, random
from fractions import Fraction
from functools import lru_cache

random.seed(298)


@lru_cache(maxsize=None)
def tau_word(w):
    if len(w) == 0:
        return 1
    if len(w) % 2:
        return 0
    tot = 0
    for j in range(1, len(w)):
        if w[j] == w[0]:
            a, b = tau_word(w[1:j]), tau_word(w[j + 1:])
            if a and b:
                tot += a * b
    return tot


def padd(p, q, c=1):
    r = dict(p)
    for w, v in q.items():
        r[w] = r.get(w, 0) + c * v
        if r[w] == 0:
            del r[w]
    return r


def pmul(p, q):
    r = {}
    for w1, a in p.items():
        for w2, b in q.items():
            w = w1 + w2
            r[w] = r.get(w, 0) + a * b
    return {w: v for w, v in r.items() if v != 0}


def tau(p):
    return sum(Fraction(v) * tau_word(w) for w, v in p.items())


def d_u(p):
    """Free difference quotient in u (vanishing on t): list of (left,right,coef)."""
    out = []
    for w, v in p.items():
        for i, ch in enumerate(w):
            if ch == 'u':
                out.append((w[:i], w[i + 1:], v))
    return out


def rand_poly(maxdeg=4, terms=4):
    p = {}
    for _ in range(terms):
        L = random.randint(0, maxdeg)
        w = ''.join(random.choice('ut') for _ in range(L))
        p[w] = p.get(w, 0) + random.randint(-3, 3)
    return {w: v for w, v in p.items() if v != 0} or {'': 1}


def mono(w, c=1):
    return {w: c}


def check_scalar(q, x, y):
    lhs = Fraction(0)
    for l, r, c in d_u(q):
        lhs += c * tau(pmul(mono(l), x)) * tau(pmul(y, mono(r)))
    # (tau (x) 1) d_u x  and (1 (x) tau) d_u y
    tx = {}
    for l, r, c in d_u(x):
        tx = padd(tx, {r: c * tau_word(l)})
    ty = {}
    for l, r, c in d_u(y):
        ty = padd(ty, {l: c * tau_word(r)})
    Xi = padd(pmul(pmul(y, mono('u')), x), pmul(y, tx), -1)
    Xi = padd(Xi, pmul(ty, x), -1)
    rhs = tau(pmul(Xi, q))
    return lhs, rhs, Xi


# ---- matrix-valued polynomials: dict (i,j) -> poly ----
def mmul(P, Q, k):
    R = {}
    for (i, j), p in P.items():
        for (l, m), q in Q.items():
            if j == l:
                R[(i, m)] = padd(R.get((i, m), {}), pmul(p, q))
    return {key: v for key, v in R.items() if v}


def mtr(P, k):
    return sum(tau(p) for (i, j), p in P.items() if i == j) / Fraction(k)


def Delta(P, b, c, x, y, k):
    """Delta_bc[x(x)y](P) as list of (A,B) matrix-poly pairs (first leg, second leg)."""
    out = []
    for (i, j), p in P.items():
        for l, r, coef in d_u(p):
            for s in range(k):
                # (E_ij (x) l)(E_sb (x) x) (x) (E_cs (x) y)(1 (x) r)
                if j != s:
                    continue
                A = {(i, b): pmul({l: coef}, x)}
                Bm = {(c, s): pmul(y, mono(r))}
                out.append((A, Bm))
    return out


def pair_trace(terms, k):
    return sum(mtr(A, k) * mtr(B, k) for A, B in terms)


def checks(k=2, trials=6):
    res = {"scalar": [], "matrix": [], "leibniz": []}
    for _ in range(trials):
        q, x, y = rand_poly(), rand_poly(3, 3), rand_poly(3, 3)
        lhs, rhs, _ = check_scalar(q, x, y)
        res["scalar"].append(lhs == rhs)
        P = {(random.randrange(k), random.randrange(k)): rand_poly() for _ in range(3)}
        b, c = random.randrange(k), random.randrange(k)
        lhsM = pair_trace(Delta(P, b, c, x, y, k), k)
        _, _, Xi = check_scalar({'': 1}, x, y)
        rhsM = mtr(mmul({(c, b): Xi}, P, k), k) / k
        res["matrix"].append(lhsM == rhsM)
        # Leibniz: Delta(PQ) vs Delta(P)Q + P Delta(Q), compared through a
        # separating family of pair-trace functionals with random test matrices.
        Q = {(random.randrange(k), random.randrange(k)): rand_poly(3, 2) for _ in range(2)}
        PQ = mmul(P, Q, k)
        ok = True
        for _t in range(3):
            L1 = {(random.randrange(k), random.randrange(k)): rand_poly(2, 2)}
            L2 = {(random.randrange(k), random.randrange(k)): rand_poly(2, 2)}
            def F(terms):
                return sum(mtr(mmul(L1, A, k), k) * mtr(mmul(B, L2, k), k) for A, B in terms)
            left = F(Delta(PQ, b, c, x, y, k))
            right = F([(A, mmul(B, Q, k)) for A, B in Delta(P, b, c, x, y, k)]) + \
                F([(mmul(P, A, k), B) for A, B in Delta(Q, b, c, x, y, k)])
            ok = ok and (left == right)
        res["leibniz"].append(ok)
    # centrality of the inserted value w_bc#(x(x)y): E_pq . v = v . E_pq
    # v = sum_s E_sb (x) E_cs; left action on first leg, right action on second.
    cent = True
    for p_ in range(k):
        for q_ in range(k):
            for b in range(k):
                for c in range(k):
                    v = [((s, b), (c, s)) for s in range(k)]
                    leftv = sorted(((p_, j0), (i1, j1)) for (i0, j0), (i1, j1) in v if i0 == q_)
                    rightv = sorted(((i0, j0), (i1, q_)) for (i0, j0), (i1, j1) in v if j1 == p_)
                    cent = cent and leftv == rightv and len(leftv) == 1
    res["centrality"] = cent
    # Negative controls: each mutation must fail in at least one trial.
    mut_transpose, mut_nocorr = False, False
    for _ in range(trials):
        q, x, y = rand_poly(), rand_poly(3, 3), rand_poly(3, 3)
        P = {(random.randrange(k), random.randrange(k)): rand_poly() for _ in range(3)}
        b, c = 0, 1
        lhsM = pair_trace(Delta(P, b, c, x, y, k), k)
        _, _, Xi = check_scalar({'': 1}, x, y)
        if lhsM != mtr(mmul({(b, c): Xi}, P, k), k) / k:
            mut_transpose = True
        Xi0 = pmul(pmul(y, mono('u')), x)
        if check_scalar(q, x, y)[0] != tau(pmul(Xi0, q)):
            mut_nocorr = True
    res["control_transposed_unit_detected"] = mut_transpose
    res["control_dropped_correction_detected"] = mut_nocorr
    return res


if __name__ == '__main__':
    out = {}
    for k in [2, 3]:
        r = checks(k)
        out[f"k={k}"] = {key: (all(v) if isinstance(v, list) else v) for key, v in r.items()}
        out[f"k={k}"]["trials"] = len(r["scalar"])
    assert all(all(v for kk, v in d.items() if kk != 'trials') for d in out.values()), out
    out["scope"] = "exact rational finite identities only; no entropy or existence claim"
    print(json.dumps(out, indent=1))

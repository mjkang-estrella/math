#!/usr/bin/env python3
"""
certify_odd.py -- variant of certify_gen.py for kappa0 with odd offsets: certifies g(S(x,y,z)) = (z+1) mod 2 (z >= z0),
for an arbitrary pair 1 <= x < y, following Section 5 of REPORT.md (Lemmas P', W', M').

All values are computed with Proposition 6.1 / Theorem 4.3 (function Gamma below).  The program
checks the finitely many hypotheses of the lemmas; if it prints "ALL HYPOTHESES VERIFIED" then
g(S(x,y,z)) = z mod 2 for every z >= z0, with z0 printed (and z0-1 a genuine exception if z0>1).

Hypotheses checked
 (G1) every blocked family V_kappa^phi (kappa reachable short configuration, phi in {I,O}) has an
      arithmetic-periodic closed form  V(r) = d_kappa * r + q_kappa^phi(r mod PI)  for r >= r0,
      d_kappa in {0,1} the same for both phi; checked against Gamma for all r <= RMAX.
 (G2) Lemma P' : RMAX+1 >= R_P = max(2*PI+1+rhat, PI+MP+D-lam+1).
 (G3) Lemma W' (each type-L kappa): residue cover (W1a), bottom cover (W1b) for every residue class
      of R mod PI at a representative R >= R_W, and RMAX+1 >= R_W + Q.
 (G4) Lemma M' : kappa0=(n,{(x,*),(y,*)}) is of type L with q constant = c, c even, same initial
      values for both phi; every short-leg successor of kappa0 is of type P and has cut
      certificates; z1 computed.
 Then g(S(x,y,z)) is computed directly for z < z1 (+40 for sanity).
Usage: python3 certify_gen.py x y [RMAX]
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(1000000)


def rho(k, delta, phi):
    if k == 0:
        return 0
    if phi == '*':
        return k
    if phi == delta:
        return k % 2
    return 1 if (k >= 2 and k % 2 == 0) else 0


def rho_free(k, phi):
    if k == 0:
        return 0
    return k % 2 if phi == '*' else k


def dot(s, delta):
    if delta == 'I':
        return {'n': 'i', 'i': 'i', 'o': 'f', 'f': 'f'}[s]
    return {'n': 'o', 'o': 'o', 'i': 'f', 'f': 'f'}[s]


def mex(S):
    g = 0
    while g in S:
        g += 1
    return g


@lru_cache(maxsize=None)
def Gamma(s, L):
    if len(L) == 0:
        return 0
    if s == 'f':
        v = 0
        for (h, phi) in L:
            v ^= rho_free(h, phi)
        return v
    if s in ('i', 'o') and len(L) == 1:
        (h, phi), = L
        return rho(h, 'O' if s == 'i' else 'I', phi)
    opts = set()
    for idx, (h, phi) in enumerate(L):
        rest = L[:idx] + L[idx + 1:]
        for j in range(1, h + 1):
            for delta in ('I', 'O'):
                if j == h and phi != '*' and delta != phi:
                    continue
                det = rho(h - j, delta, phi)
                if j >= 2:
                    val = Gamma(s, tuple(sorted(rest + ((j - 1, delta),))))
                else:
                    val = Gamma(dot(s, delta), rest)
                opts.add(det ^ val)
    return mex(opts)


def short_moves(kappa):
    s, K = kappa
    for idx, (h, phi) in enumerate(K):
        rest = K[:idx] + K[idx + 1:]
        for j in range(1, h + 1):
            for delta in ('I', 'O'):
                if j == h and phi != '*' and delta != phi:
                    continue
                det = rho(h - j, delta, phi)
                if j >= 2:
                    yield det, 'a1', (s, tuple(sorted(rest + ((j - 1, delta),))))
                else:
                    s2 = dot(s, delta)
                    if s2 == 'f':
                        yield det, 'a2', rest
                    elif len(rest) == 0:
                        yield det, 'a3', s2
                    else:
                        yield det, 'a1', (s2, rest)


def reachable(x, y):
    start = ('n', tuple(sorted(((x, '*'), (y, '*')))))
    seen, stack = {start}, [start]
    while stack:
        k = stack.pop()
        for det, kind, data in short_moves(k):
            if kind == 'a1' and data not in seen:
                seen.add(data)
                stack.append(data)
    return start, seen


def V(kappa, phi, r):
    s, K = kappa
    return Gamma(s, tuple(sorted(K + ((r, phi),))))


def xorbit(x, b):
    """x XOR b for b in {0,1}, valid also as an offset formula"""
    return x + b - 2 * b * (x % 2)


def main():
    x, y = int(sys.argv[1]), int(sys.argv[2])
    RMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    ok = True

    def fail(msg):
        nonlocal ok
        ok = False
        print('FAIL:', msg)

    k0, confs = reachable(x, y)
    confs = sorted(confs)
    print('pair (%d,%d): %d reachable short configurations, RMAX=%d' % (x, y, len(confs), RMAX))
    vals = {}
    for r in range(1, RMAX + 1):            # increasing r keeps recursion shallow
        for k in confs:
            for p in 'IO':
                vals.setdefault((k, p), [None]).append(V(k, p, r))

    # ---------------- (G1) fit arithmetic-periodic forms
    form = {}
    for k in confs:
        for p in 'IO':
            v = vals[(k, p)]
            best = None
            for per in (1, 2, 4, 8, 16, 32):
                for d in (0, 1):
                    r0 = RMAX - per
                    while r0 >= 1 and v[r0 + per] == v[r0] + d * per:
                        r0 -= 1
                    r0 += 1
                    if r0 <= RMAX - 3 * per - 40:
                        if best is None:
                            best = (per, d, r0)
                if best:
                    break
            if best is None:
                fail('no arithmetic-periodic form for %s %s' % (k, p))
                continue
            form[(k, p)] = best
    if not ok:
        print('RESULT (%d,%d): FAILED' % (x, y)); return 1
    PI = max([2] + [f[0] for f in form.values()])   # PI is a power of 2 and even
    typ, q, r0 = {}, {}, {}
    for k in confs:
        ds = {form[(k, p)][1] for p in 'IO'}
        if len(ds) != 1:
            fail('mixed type for %s' % (k,))
            continue
        typ[k] = 'L' if ds.pop() == 1 else 'P'
        for p in 'IO':
            per, d, rr = form[(k, p)]
            r0[(k, p)] = rr
            # q indexed by r mod PI
            q[(k, p)] = [None] * PI
            for res in range(PI):
                r = rr + ((res - rr) % PI)
                q[(k, p)][res] = v_ = vals[(k, p)][r] - d * r
    if not ok:
        print('RESULT (%d,%d): FAILED' % (x, y)); return 1

    def closed(k, p, r):
        if r < r0[(k, p)]:
            return vals[(k, p)][r]
        return (r if typ[k] == 'L' else 0) + q[(k, p)][r % PI]

    for k in confs:
        for p in 'IO':
            for r in range(1, RMAX + 1):
                if closed(k, p, r) != vals[(k, p)][r]:
                    fail('form mismatch %s %s r=%d' % (k, p, r))
    # dump the closed forms (list of closed forms with their ranges of validity)
    def fmt(k):
        s, K = k
        return s + '{' + ','.join('%d%s' % (h, p) for (h, p) in K) + '}'
    with open('forms_%d_%d.txt' % (x, y), 'w') as fh:
        fh.write('# closed forms of the blocked families of S(%d,%d,.): V(r) = slope*r + q[r mod %d] for r >= r0;\n'
                 '# initial values V(1..r0-1) listed.  I = IN (towards centre), O = OUT.  Verified for r <= %d,\n'
                 '# valid for all r by Lemmas P/L (if the certificate run printed ALL HYPOTHESES VERIFIED).\n' % (x, y, PI, RMAX))
        for k in confs:
            for p in 'IO':
                fh.write('%-22s phi=%s type=%s slope=%d r0=%-3d q=%s init=%s\n' % (
                    fmt(k), p, typ[k], 1 if typ[k] == 'L' else 0, r0[(k, p)], q[(k, p)],
                    vals[(k, p)][1:r0[(k, p)]]))
    nL = sum(1 for k in confs if typ[k] == 'L')
    rhat = max(r0.values())
    MP = max(max(vals[(k, p)][1:]) for k in confs for p in 'IO' if typ[k] == 'P')
    D = max([det for k in confs for det, kind, data in short_moves(k)] + [0])
    lam = min([0] + [min(q[(k, p)]) for k in confs for p in 'IO' if typ[k] == 'L'])
    print('(G1) period PI=%d, %d type-L configurations, rhat=%d, MP=%d, D=%d, lambda=%d' % (PI, nL, rhat, MP, D, lam))

    # ---------------- (G2) Lemma P'
    RP = max(2 * PI + 1 + rhat, PI + MP + D - lam + 1)
    print("(G2) Lemma P' applies for R >= %d" % RP)
    if RMAX + 1 < RP:
        fail('(G2) RMAX too small')

    # ---------------- (G3) Lemma W' for each type-L configuration
    Q = PI
    while Q <= D:
        Q *= 2
    W_needed = 0
    for k in confs:
        if typ[k] != 'L':
            continue
        rk = max(r0[(k, 'I')], r0[(k, 'O')])
        # offsets e(iota, delta, rho, phi)
        E = {}
        for p in 'IO':
            for rr in (0, 1):
                for io in range(PI):
                    for d in 'IO':
                        qq = q[(k, d)][io]
                        bit = ((rr - 1 - io) % 2) ^ (1 if d != p else 0)
                        E[(p, rr, io, d)] = xorbit(io + qq, bit) - io
                # (W1a) residue cover
                res = {(io + E[(p, rr, io, d)]) % PI for io in range(PI) for d in 'IO'}
                if len(res) != PI:
                    fail("(W1a) residue cover fails for %s phi=%s R%%2=%d" % (k, p, rr))
        emin, emax = min(E.values()), max(E.values())
        qmax = max(max(q[(k, d)]) for d in 'IO')
        qmin = min(min(q[(k, d)]) for d in 'IO')
        low = rk + emax
        Kc = 2 - emin
        M = qmax + Kc + 1
        imax = max(low - qmin + 1, rk)
        maxinit = max([vals[(k, d)][i] for d in 'IO' for i in range(1, rk)] + [0])
        # small options bound, computed at representatives
        smallmax = 0
        Rrep0 = max(rhat, imax) + 2 + PI
        for R in range(Rrep0, Rrep0 + PI):
            for p in 'IO':
                for det, kind, data in short_moves(k):
                    if kind == 'a1' and typ[data] == 'P':
                        smallmax = max(smallmax, det ^ closed(data, p, R))
                    elif kind == 'a3':
                        smallmax = max(smallmax, det ^ rho(R, 'O' if data == 'i' else 'I', p))
                for d in 'IO':
                    smallmax = max(smallmax, rho(R - 1, d, p) ^ Gamma(dot(k[0], d), k[1]))
        RW = max(rk + M, smallmax + Kc + 1, maxinit + Kc + 2, imax + 2, rhat + PI + 1, Rrep0)
        # (W1b) bottom cover at representatives of every class of R mod PI
        for R in range(RW, RW + PI):
            for p in 'IO':
                S = set()
                for det, kind, data in short_moves(k):
                    if kind == 'a1' and typ[data] == 'P':
                        S.add(det ^ closed(data, p, R))
                    elif kind == 'a3':
                        S.add(det ^ rho(R, 'O' if data == 'i' else 'I', p))
                for d in 'IO':
                    S.add(rho(R - 1, d, p) ^ Gamma(dot(k[0], d), k[1]))
                for i in range(1, imax + 1):
                    for d in 'IO':
                        S.add(closed(k, d, i) ^ rho(R - 1 - i, d, p))
                miss = set(range(low)) - S
                if miss:
                    fail('(W1b) bottom cover fails for %s phi=%s R=%d missing %s' % (k, p, R, sorted(miss)[:10]))
        W_needed = max(W_needed, RW + Q)
    print("(G3) Lemma W' applies for R >= %d (Q=%d)" % (W_needed, Q))
    if RMAX + 1 < W_needed:
        fail('(G3) RMAX too small')

    # ---------------- (G4-odd) variant of Lemma M' for kappa0 = r + q(r mod PI) with all q odd
    # Target: g(S(x,y,z)) = (z+1) mod 2.  Cuts of kappa0 with i >= r0 have the parity of z;
    # the zero option for even z is supplied by a short move with d = 1 to (i,{1*}) or (o,{1*})
    # (Lemma F1: its free value is (z+1) mod 2, so the option is z mod 2).
    if typ[k0] != 'L' or q[(k0, 'I')] != q[(k0, 'O')] or any(qq % 2 == 0 for qq in q[(k0, 'I')]):
        fail('(G4-odd) kappa0 offsets not all odd / not equal for I,O')
        print('RESULT (%d,%d): FAILED' % (x, y)); return 1
    rk0 = max(r0[(k0, 'I')], r0[(k0, 'O')])
    W = {d: Gamma(dot('n', d), k0[1]) for d in 'IO'}
    thr = {'cutsmall': max([i + max(vals[(k0, d)][i] for d in 'IO') + 3 for i in range(1, rk0)] + [0]),
           'longj1': max(W.values()) + 3}
    zc = 0
    zero_provider = False
    for det, kind, sig in short_moves(k0):
        if kind == 'a1' and typ[sig] == 'L' and sig in (('i', ((1, '*'),)), ('o', ((1, '*'),))):
            par_ok = all((vals[(sig, d)][i] - i) % 2 == 1 for d in 'IO' for i in range(1, r0[(sig, d)])) and \
                all(qq % 2 == 1 for d in 'IO' for qq in q[(sig, d)])
            if not par_ok or det == 0:
                fail('(G4-odd) Lemma F1 successor %s with det %d not usable' % (sig, det))
            else:
                if det == 1:
                    zero_provider = True
                print('(G4-odd) successor %s handled by Lemma F1 (det %d)' % (sig, det))
            continue
        if kind != 'a1' or typ[sig] != 'P':
            fail('(G4-odd) successor %s of kappa0 not of type P' % (sig,))
            continue
        need = det | 1
        qm = max(max(q[(sig, d)]) for d in 'IO')
        for par in range(2 * PI):
            for v in range(need + 1):
                found = None
                for t in range(0, 2 * max(qm, need) + 2 * PI + 3):
                    for d in 'IO':
                        res = (par - 1 - t) % PI
                        if t ^ q[(sig, d)][res] == v:
                            cand = t + 1 + r0[(sig, d)]
                            if found is None or cand < found:
                                found = cand
                if found is None:
                    fail('(G4-odd) no certificate: succ %s det %d z=%d mod %d value %d' % (sig, det, par, 2 * PI, v))
                    continue
                zc = max(zc, found)
    if not zero_provider:
        fail('(G4-odd) no zero provider for even z')
    thr['succ'] = zc
    z1 = max(thr.values())
    print("(G4-odd) kappa0 offsets %s for r >= %d; W = %s; thresholds %s => z1 = %d" % (q[(k0, 'I')], rk0, W, thr, z1))
    gz = {z: Gamma('n', tuple(sorted(((x, '*'), (y, '*'), (z, '*'))))) for z in range(1, z1 + 41)}
    bad = [z for z in gz if gz[z] != (z + 1) % 2]
    z0 = max(bad) + 1 if bad else 1
    if any(gz[z] != (z + 1) % 2 for z in range(z1, z1 + 41)):
        fail('sanity: disagreement above z1')
    print('first values:', [gz[z] for z in range(1, min(40, z1 + 40) + 1)])
    print('RESULT (%d,%d): ' % (x, y) + ('ALL HYPOTHESES VERIFIED (target (z+1) mod 2), z0 = %d, z1 = %d' % (z0, z1) if ok else 'FAILED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())

# v2-squeeze closure for 'u' (unresolved) classes of gen_nd certificates.
#
# Setting: X = 10^L + sum_i A_i 10^{q_i} + K = 2^t0 3^a 7^w  (t0 = v2(K), C = K/2^t0 odd),
# domain L > q_{D-1} > ... > q_1 >= qmin.  A class (r, M) with sig a >= a_lo (unbounded),
# w = w0 EXACT (7 does not divide X at the class rep, and 6 | M so this holds class-wide).
#
# For any solution point in the class:
#  (pin)    X == K (mod 10^{q1})  =>  3^a == C*7^{-w0} (mod 5^{q1})  =>  a == rho (mod 4),
#           rho = dlog_3(C*7^{-w0} mod 5)   [3 is a primitive root mod 5^k]
#  (squeeze) 2^t0 (3^a 7^{w0} - C) = 10^{q1} (10^{L-q1} + A1 + A2 10^{q2-q1} + ...)
#           =>  v2(3^a 7^{w0} - C) = q1 + s - t0,   s = v2(10^{L-q1} + A1 + ...),  s >= s_min
#  with a == rho (mod 4) fixed, v2(3^a 7^{w0} - C) = beta is a CONSTANT
#  (beta = v2( 3^rho 7^{w0 mod 4} - C ) mod 16, valid when 3^rho 7^{w0} != C mod 16).
#  Hence q1 = beta + t0 - s <= Q := beta + t0 - s_min:  q1 is BOUNDED.
#  All class points have q1 == r1 (mod M); if the least such q1 >= qmin exceeds Q, the
#  class contains no solution.  Otherwise the class reduces to the single slice q1 = minq,
#  which is a 1-D (or lower-dim) problem: K' = A1*10^q1 + K.
#
# usage: python3 -I squeeze.py cert.jsonl [--json out.json]
import sys, json

def vp(x, p):
    if x == 0: return 10**9
    n = 0
    while x % p == 0: x //= p; n += 1
    return n

def dlog3(c, mod=5):
    for r in range(4):
        if pow(3, r, mod) == c % mod: return r
    return None

def squeeze_node(meta, nd):
    """Return (verdict, info). verdict in {'KILLED','SLICE','FAIL'}."""
    DIM, COEFS, K, QMIN = meta['dim'], meta['coefs'], meta['K'], meta['qmin']
    t0 = vp(K, 2); C = K >> t0
    a, w = nd['a'], nd['w']
    r, M = nd['r'], nd['m']
    assert a[1] is None, "squeeze needs a unbounded"
    if w[1] is not None: w0 = w[0]
    else: return ('FAIL', {'why': 'w unbounded at class'})
    # pin mod 5
    rho = dlog3(C * pow(7, -w0, 5) if w0 else C, 5) if False else dlog3((C * pow(pow(7, w0, 5), -1, 5)) % 5, 5)
    if rho is None: return ('KILLED', {'why': 'mod-5 pin unsolvable'})
    # mod-8 pin kill (3^a 7^w0 == C mod 2^{q1-t0}; <3> mod 2^m = {1,3} mod 8)
    x8 = (C * pow(7, w0, 8)) % 8
    if x8 not in (1, 3) and minq_of(r[1], M, QMIN) - t0 >= 3:
        return ('KILLED', {'why': 'mod-2 pin unsolvable', 'x8': x8})
    # beta
    r16 = (pow(3, rho, 16) * pow(7, w0 % 4, 16)) % 16
    d = (r16 - C) % 16
    if d == 0: return ('FAIL', {'why': 'beta unbounded (3^rho 7^w0 == C mod 16)'})
    beta = vp(d, 2)
    # s_min over m1 in [1,60], m2 in (m1, 61] (v2(A_i) <= 3 << 60, so asymptote covered)
    A1 = COEFS[0]
    assert all(vp(A, 2) <= 3 for A in COEFS)
    smin = 10**9
    if DIM == 2:
        for m1 in range(1, 61):
            smin = min(smin, vp(pow(10, m1, 1 << 20) + A1, 2) if (pow(10, m1, 1 << 20) + A1) else 20)
        # exact large-m value:
        smin = min(smin, vp(A1, 2))
    else:
        A2 = COEFS[1]
        for m1 in range(1, 61):
            for m2 in range(m1 + 1, 62):
                g = pow(10, m1, 1 << 24) + A1 + A2 * pow(10, m2, 1 << 24)
                smin = min(smin, vp(g, 2) if g else 24)
        smin = min(smin, vp(A1, 2))
    Q = beta + t0 - smin
    mq = minq_of(r[1], M, QMIN)
    info = {'rho': rho, 'beta': beta, 'smin': smin, 'Q': Q, 'minq': mq, 'r1': r[1], 'M': M}
    if mq > Q: return ('KILLED', info)
    if mq <= Q:
        assert mq == r[1] and mq >= QMIN, (mq, r[1], M, QMIN)
        Kp = A1 * 10 ** mq + K
        info['slice_q'] = mq; info['Kprime'] = Kp
        return ('SLICE', info)
    return ('FAIL', info)

def minq_of(r1, M, qmin):
    if r1 >= qmin: return r1
    k = (qmin - r1 + M - 1) // M
    return r1 + k * M

def main():
    args = sys.argv[1:]
    outjson = None
    if '--json' in args:
        i = args.index('--json'); outjson = args[i + 1]; del args[i:i + 2]
    path = args[0]
    raw = [json.loads(l) for l in open(path) if l.strip()]
    meta = raw[0]
    uns = [n for n in raw[1:] if n['k'] == 'u']
    res = []
    cnt = {'KILLED': 0, 'SLICE': 0, 'FAIL': 0}
    for nd in uns:
        v, info = squeeze_node(meta, nd)
        cnt[v] += 1
        res.append({'id': nd['id'], 'verdict': v, **info})
    print(f"{path}: u-nodes={len(uns)} KILLED={cnt['KILLED']} SLICE={cnt['SLICE']} FAIL={cnt['FAIL']}")
    for x in res:
        if x['verdict'] != 'KILLED': print(' ', x)
    slices = sorted({(x['slice_q'], x['Kprime']) for x in res if x['verdict'] == 'SLICE'})
    if slices: print('  slices needed (q, K\'):', slices)
    if outjson:
        json.dump({'meta': meta, 'results': res}, open(outjson, 'w'), indent=1)
    if cnt['FAIL']: sys.exit(3)

if __name__ == '__main__':
    main()

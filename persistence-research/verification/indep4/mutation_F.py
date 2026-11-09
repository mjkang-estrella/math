# Sensitivity of the pin tests: wrong 2-adic handling must lose true solutions (so the positive controls could catch it).
import sys, random
sys.path.insert(0, '.')
import check_sym_F as F
rnd = random.Random(3)
def pairs(E, kt):
    A, W = F.order(3, E), F.order(7, E)
    return A, W, {(a, b) for a in range(A) for b in range(W) if pow(3, a, E) * pow(7, b, E) % E == kt % E}
res = {}
for t0 in (1, 2, 3, 4, 6, 12):
    k = 3; miss_ok = miss_nodiv = n = 0
    for _ in range(300):
        qmin = max(3, t0 + 1)      # no pin2 (needs qmin >= t0+3): only the tail info is available
        a2, w2 = rnd.randrange(60), rnd.randrange(30)
        N = (1 << t0) * 3 ** a2 * 7 ** w2
        pos = rnd.sample(range(qmin, qmin + 10), 4); L = max(pos) + 2
        X0 = 10 ** L + sum(54 * 10 ** q for q in pos)
        K = N - X0
        if K <= 0 or K % 5 == 0: continue
        kt = K >> t0; n += 1
        E_ok = 5 ** k * 2 ** max(k - t0, 0)
        E_bad = 5 ** k * 2 ** k                     # forgets to divide by 2^t0: modulus 2^k 5^k on Y
        A, W, P = pairs(E_ok, kt); miss_ok += (a2 % A, w2 % W) not in P
        A, W, P = pairs(E_bad, kt); miss_nodiv += (a2 % A, w2 % W) not in P
    res[t0] = (n, miss_ok, miss_nodiv)
    print('t0=%2d  true solutions %3d | correct modulus 5^3*2^max(3-t0,0): true pair missing %d | WRONG modulus 5^3*2^3 on K/2^t0: true pair missing %d' % (t0, n, miss_ok, miss_nodiv))

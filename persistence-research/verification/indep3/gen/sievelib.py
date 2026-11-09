# Sieve engine (generator side only; the checker re-derives everything independently).
import sys, os, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import vp, lcm
from universe import build

class Sieve:
    def __init__(self, coefs, K, qmin, pmax=20000000, MU=64*729*25*2401, cache=None):
        self.coefs, self.K, self.qmin = list(coefs), K, qmin
        self.dim = len(coefs) + 1
        self.t0 = vp(K, 2)
        assert qmin > self.t0 and K % 5 != 0
        U = build(pmax, MU, cache)
        self.PT = collections.defaultdict(list)
        for (p, d, o3, o7) in U:
            H = lcm(o3, o7); idx = (p - 1) // H
            tb = [1] * d
            if d <= 20000:
                for e in range(1, d): tb[e] = tb[e - 1] * 10 % p
            else: tb = None
            self.PT[d].append((idx, p, o3, o7, H, pow(2, -self.t0, p), tb))
        for d in self.PT: self.PT[d].sort(key=lambda e: (-e[0], e[1]))
        self._al = {}
        self._inv = {}
    def Xmod(self, r, m):
        s = pow(10, r[0], m) + self.K
        for c, e in zip(self.coefs, r[1:]): s += c * pow(10, e, m)
        return s % m
    def sig(self, r, M):
        j = vp(M, 3); m3 = 3 ** (j + 2)
        x = self.Xmod(r, m3)
        a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
        if M % 6 == 0:
            i = vp(M, 7); m7 = 7 ** (i + 1)
            x = self.Xmod(r, m7)
            w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
        else: w = (0, None)
        return a, w
    def aligned(self, M):
        v = self._al.get(M)
        if v is None:
            lst = []
            for d, L in self.PT.items():
                if M % d == 0: lst.extend((d,) + e for e in L)
            lst.sort(key=lambda e: (-e[1], e[2], e[0]))   # strongest (largest index) first
            self._al[M] = v = lst
        return v
    def inv(self, g, e, p):
        k = (g, e, p); v = self._inv.get(k)
        if v is None: v = self._inv[k] = pow(g, -e, p)
        return v
    def kill_by(self, r, M, a, w):
        af, wf = a[1] is None, w[1] is None
        a0, w0 = a[0], w[0]
        K, coefs = self.K, self.coefs
        for d, idx, p, o3, o7, H, i2, tb in self.aligned(M):
            if tb is not None:
                T = K + tb[r[0] % d]
                for c, e in zip(coefs, r[1:]): T += c * tb[e % d]
            else:
                T = K + pow(10, r[0] % d, p)
                for c, e in zip(coefs, r[1:]): T += c * pow(10, e % d, p)
            T = T % p * i2 % p
            if T == 0: return p
            x = T * self.inv(3, a0, p) % p * self.inv(7, w0, p) % p
            if af and wf:
                if idx > 1 and pow(x, H, p) != 1: return p
            elif af:
                if pow(x, o3, p) != 1: return p
            elif wf:
                if pow(x, o7, p) != 1: return p
            else:
                if x != 1: return p
        return None
    def lifts(self, r, M, M2):
        f = M2 // M
        for t in itertools.product(range(f), repeat=self.dim):
            yield tuple((x % M) + k * M for x, k in zip(r, t))
    def in_domain_points(self, N):
        res = []; K, coefs, QMIN = self.K, self.coefs, self.qmin
        D = len(str(N)) + 1
        if self.dim == 1:
            for L in range(QMIN, D + 1):
                if 10 ** L + K == N: res.append((L,))
        elif self.dim == 2:
            for L in range(2, D + 1):
                for q in range(QMIN, L):
                    if 10 ** L + coefs[0] * 10 ** q + K == N: res.append((L, q))
        else:
            for q2 in range(QMIN + 1, D + 1):
                for q1 in range(QMIN, q2):
                    R = N - K - coefs[0] * 10 ** q1 - coefs[1] * 10 ** q2
                    if R > 0:
                        s = str(R)
                        if s == '1' + '0' * (len(s) - 1) and len(s) - 1 > q2: res.append((len(s) - 1, q1, q2))
        return res

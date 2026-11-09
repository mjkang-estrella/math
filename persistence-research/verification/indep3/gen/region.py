# Region logic shared by the checker and the soundness tests (independent of any parent/agent code).
import itertools
from nt import vp, order, lcm, isprime

class Region:
    def __init__(self, coefs, K):
        self.coefs, self.K = list(coefs), K
        self.dim = len(coefs) + 1
        self.t0 = vp(K, 2)
    def Xmod(self, r, m):
        s = pow(10, r[0], m) + self.K
        for c, e in zip(self.coefs, r[1:]): s += c * pow(10, e, m)
        return s % m
    def sig(self, r, M):
        j = vp(M, 3); m3 = 3 ** (j + 2)
        assert pow(10, 3 ** j, m3) == 1
        x = self.Xmod(r, m3)
        a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
        if M % 6 == 0:
            i = vp(M, 7); m7 = 7 ** (i + 1)
            assert pow(10, 6 * 7 ** i, m7) == 1
            x = self.Xmod(r, m7)
            w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
        else: w = (0, None)
        return a, w
    def lifts(self, r, M, M2):
        f = M2 // M
        for t in itertools.product(range(f), repeat=self.dim):
            yield tuple((x % M) + k * M for x, k in zip(r, t))
    def kill_prime(self, p, r, M):
        """True iff every (L,q..) in class r mod M, for which X = 2^t0 3^a 7^w with (a,w) in the class signature, is excluded mod p."""
        assert isprime(p) and p > 7
        d = order(10, p)
        if M % d:
            M2 = lcm(M, d)
            return all(self.kill_prime(p, r2, M2) for r2 in self.lifts(r, M, M2))
        a, w = self.sig(r, M)
        T = self.Xmod([x % d for x in r], p) * pow(2, -self.t0, p) % p
        if T == 0: return True
        o3, o7 = order(3, p), order(7, p)
        x = T * pow(3, -a[0], p) * pow(7, -w[0], p) % p
        af, wf = a[1] is None, w[1] is None
        if af and wf: return pow(x, lcm(o3, o7), p) != 1
        if af: return pow(x, o3, p) != 1
        if wf: return pow(x, o7, p) != 1
        return x != 1

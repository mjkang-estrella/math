# exploratory BFS sieve: survivors per refinement level for a fixed schedule
import sys, os, json, math, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import vp

class Engine:
    def __init__(self, coefs, K, supply, maxp=None):
        self.coefs = list(coefs); self.dim = len(coefs) + 1; self.K = K
        self.t0 = vp(K, 2)
        self.byd = {}
        for p, d, o3, o7 in supply:
            if maxp and p > maxp: continue
            H = o3 * o7 // math.gcd(o3, o7)
            self.byd.setdefault(d, []).append((p, d, o3, o7, H))
        self.tabs = {}
        self._al = {}
    def aligned(self, M):
        if M not in self._al:
            v = []
            for d, L in self.byd.items():
                if M % d == 0:
                    for (p, d, o3, o7, H) in L:
                        pw = [pow(10, r, p) for r in range(d)]
                        cw = [[c * x % p for x in pw] for c in self.coefs]
                        v.append(((p - 1) // H, p, d, o3, o7, H, pw, cw, pow(2, -self.t0, p)))
            v.sort(key=lambda e: -e[0] * 1000 - (e[1] - 1) // e[3])
            self._al[M] = v
        return self._al[M]
    def modtab(self, m, per):
        k = (m, per)
        if k not in self.tabs:
            pw = [pow(10, r, m) for r in range(per)]
            self.tabs[k] = (pw, [[c * x % m for x in pw] for c in self.coefs])
        return self.tabs[k]
    def sig(self, r, M):
        j = vp(M, 3); m3 = 3 ** (j + 2); per = 3 ** j
        pw, cw = self.modtab(m3, per)
        x = (pw[r[0] % per] + self.K + sum(cw[i][r[i + 1] % per] for i in range(self.dim - 1))) % m3
        a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
        if M % 6 == 0:
            i = vp(M, 7); m7 = 7 ** (i + 1); per = 6 * 7 ** i
            pw, cw = self.modtab(m7, per)
            x = (pw[r[0] % per] + self.K + sum(cw[ii][r[ii + 1] % per] for ii in range(self.dim - 1))) % m7
            w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
        else: w = (0, None)
        return a, w
    def kill(self, r, M, a, w, al):
        af, wf = a[1] is None, w[1] is None
        for (idx, p, d, o3, o7, H, pw, cw, i2) in al:
            if not (af or wf) and False: pass
            T = (pw[r[0] % d] + self.K + sum(cw[i][r[i + 1] % d] for i in range(self.dim - 1))) * i2 % p
            if T == 0: return p
            x = T * pow(3, -a[0], p) * pow(7, -w[0], p) % p
            if af and wf:
                if idx > 1 and pow(x, H, p) != 1: return p
            elif af:
                if pow(x, o3, p) != 1: return p
            elif wf:
                if pow(x, o7, p) != 1: return p
            elif x != 1: return p
        return None
    def refine(self, surv, M, f, workers=30):
        M2 = M * f; self.aligned(M2)
        if len(surv) * f ** self.dim > 200000 and workers > 1:
            import multiprocessing as mp
            global _E; _E = (self, M, f)
            chunks = [surv[i::workers * 4] for i in range(workers * 4)]
            with mp.get_context("fork").Pool(workers) as pool:
                parts = pool.map(_refine_chunk, chunks)
            return M2, [x for pp in parts for x in pp]
        return M2, self.refine_serial(surv, M, f)
    def refine_serial(self, surv, M, f):
        M2 = M * f; al = self.aligned(M2); out = []
        for r in surv:
            for t in itertools.product(range(f), repeat=self.dim):
                r2 = tuple(x + k * M for x, k in zip(r, t))
                a, w = self.sig(r2, M2)
                if self.kill(r2, M2, a, w, al) is None: out.append((r2, a, w))
        return out

_E = None
def _refine_chunk(ch):
    E, M, f = _E
    return E.refine_serial(ch, M, f)

if __name__ == "__main__":
    coefs = eval(sys.argv[1]); K = int(sys.argv[2]); sched = eval(sys.argv[3])
    sup = json.load(open(sys.argv[4]))
    cap = int(sys.argv[5]) if len(sys.argv) > 5 else 200000
    E = Engine(coefs, K, sup)
    surv, M = [(0,) * E.dim], 1
    t = time.time()
    for f in sched:
        M, out = E.refine(surv, M, f)
        from collections import Counter
        c = Counter((a[1] is None, w[1] is None) for _, a, w in out)
        print(f"M={M} f={f} alive={len(out)} (aU,wU):{dict(c)} aligned={len(E.aligned(M))} {time.time()-t:.0f}s", flush=True)
        surv = [r for r, a, w in out]
        if not surv or len(surv) > cap: break

# Prime universe: primes p (7 < p <= PMAX) whose ord_p(10) divides MU.  Computed once, cached to /tmp.
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import order, lcm
def build(PMAX, MU, cache=None):
    if cache and os.path.exists(cache): return [tuple(x) for x in json.load(open(cache))]
    sv = bytearray([1]) * (PMAX + 1)
    sv[0] = sv[1] = 0
    for p in range(2, int(PMAX ** 0.5) + 1):
        if sv[p]:
            sv[p * p::p] = bytearray(len(range(p * p, PMAX + 1, p)))
    out = []
    for p in range(11, PMAX + 1):
        if sv[p] and pow(10, MU, p) == 1:
            d = order(10, p); o3 = order(3, p); o7 = order(7, p)
            out.append((p, d, o3, o7))
    if cache: json.dump(out, open(cache, 'w'))
    return out
if __name__ == '__main__':
    import time
    PMAX = int(sys.argv[1]); MU = int(sys.argv[2])
    t = time.time(); U = build(PMAX, MU, sys.argv[3] if len(sys.argv) > 3 else None)
    idx2 = [u for u in U if (u[0] - 1) // lcm(u[2], u[3]) >= 2]
    print(len(U), "primes;", len(idx2), "with index>=2;", f"{time.time()-t:.1f}s")

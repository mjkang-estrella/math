# Prime supply: primes p > 7 with ord_p(10) = d for d in a chosen divisor set.
#   small d (phi(d) <= PHI_FACT): partial factorization of Phi_d(10) (rho), keep p <= PCAP
#   large d: primes p = 1 + d t <= B (bytearray sieve), ord_p(10) == d exactly
# output: JSON list of [p, d, o3, o7] (cache file).  Only soundness-irrelevant data: every
# certificate kill is re-verified by the checkers from scratch.
import sys, os, json, math, time
import multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import is_prime, factor_partial, factorint, order, cyclotomic_value, divisors

PCAP = 10 ** 12
PHI_FACT = 72
SV = None

def entry(p, d):
    fac = factorint(p - 1)
    assert order(10, p, fac) == d
    return [p, d, order(3, p, fac), order(7, p, fac)]

def small_d(d):
    n = cyclotomic_value(d)
    fs, rest = factor_partial(n, budget=300000)
    out = []
    for p in sorted(set(fs)):
        if p <= 7 or p > PCAP: continue
        if pow(10, d, p) == 1 and order(10, p) == d:
            out.append(entry(p, d))
    return out

def large_d(args):
    d, B = args
    out = []
    p = d + 1
    # walk the progression 1 mod d using the shared sieve
    for p in range(d + 1, B + 1, d):
        if SV[p] and pow(10, d, p) == 1 and p > 7:
            if order(10, p) == d: out.append(entry(p, d))
    return out

def build(N, B, fn, workers=24):
    global SV
    ds = divisors(N)
    phis = {d: sum(1 for k in range(1, d + 1) if math.gcd(k, d) == 1) if d < 5000 else None for d in ds}
    small = [d for d in ds if d > 1 and phis[d] is not None and phis[d] <= PHI_FACT]
    large = [d for d in ds if d not in small and d > 1]
    t = time.time()
    SV = bytearray([1]) * (B + 1); SV[0] = SV[1] = 0
    for i in range(2, int(B ** .5) + 1):
        if SV[i]: SV[i * i::i] = bytearray(len(range(i * i, B + 1, i)))
    print(f"sieve {B} {time.time()-t:.0f}s; small d {len(small)} large d {len(large)}", file=sys.stderr, flush=True)
    res = []
    with mp.get_context("fork").Pool(workers) as pool:
        for r in pool.imap_unordered(small_d, small): res += r
        print(f"small done {len(res)} {time.time()-t:.0f}s", file=sys.stderr, flush=True)
        large.sort(key=lambda d: d)
        for r in pool.imap_unordered(large_d, [(d, B) for d in large], chunksize=1): res += r
    # small-d primes also below B found via factoring; dedupe
    seen = {}
    for e in res: seen[e[0]] = e
    out = sorted(seen.values())
    json.dump(out, open(fn, "w"))
    print(f"total {len(out)} primes, {time.time()-t:.0f}s", file=sys.stderr)
    return out

if __name__ == "__main__":
    N = eval(sys.argv[1]); B = int(float(sys.argv[2])); fn = sys.argv[3]
    build(N, B, fn)

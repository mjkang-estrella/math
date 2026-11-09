"""Sweep checks of Conjecture 4.5 with robust evaluator (multiprocess)."""
from multiprocessing import Pool
import sys

def worker(args):
    a, m, l, xs = args
    from eval_ks import check_point
    from mpmath import mp, mpf
    out = []
    prev_phi = None
    for x in xs:
        try:
            res = check_point(a, m, l, x)
        except Exception as e:
            out.append((float(a), float(m), float(l), float(x), 'ERR', str(e)[:60]))
            continue
        for k in ['e_lo', 'e_hi', 'di']:
            v = res[k]
            if v < -mpf(10)**(-25):
                out.append((float(a), float(m), float(l), float(x), k, float(v)))
        if prev_phi is not None:
            d = res['phi'] - prev_phi
            if d < -mpf(10)**(-20):
                out.append((float(a), float(m), float(l), float(x), 'mono', float(d)))
        prev_phi = res['phi']
    return out

if __name__ == "__main__":
    from mpmath import mpf
    xs = [mpf(2) ** k for k in range(-20, 13)]
    jobs = []
    for a in [mpf(p) / 100 for p in [5, 10, 25, 50, 75, 90, 95, 99]]:
        for m in [mpf(1) / 10, mpf(1) / 2, 1, 2, 5, 10]:
            base = m - 1 / a
            for loff in [mpf(1) / 20, mpf(1) / 2, 1, 3, 10]:
                l = base + loff
                jobs.append((a, m, l, xs))
    with Pool(8) as pool:
        results = pool.map(worker, jobs)
    bad = [b for r in results for b in r]
    print("total param combos:", len(jobs), " violations:", len(bad))
    for b in bad[:40]:
        print(b)

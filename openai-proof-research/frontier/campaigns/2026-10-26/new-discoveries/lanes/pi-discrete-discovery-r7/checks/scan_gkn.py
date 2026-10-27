import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from math import gcd
from gkn_tail2 import tail_components, contrib_series, gkn_ND, series_div_frac
import random, time

def analyze(k, n, cap=40000, samples=3000, seed=0):
    """Return dict with status for G_{k,n} >= 0 check.
    status: 'proved' (lb>0 and initial ok), 'counterexample' (m,val), 'inconclusive'."""
    m0 = n*(2*k+n-2)
    C, comps = tail_components(k, n)
    if any(s >= 2 for (_, s, _, _) in comps):
        return {"k":k,"n":n,"status":"repeated-pole", "comps":[(c,s) for c,s,_,_ in comps]}
    # f_c arrays on [0,c)
    fs = {}
    for (c, s, bs, phi) in comps:
        cs = contrib_series(c, s, bs, phi, c-1)
        fs[c] = cs
    lb = C + sum(min(fs[c]) for c in fs)
    # initial segment exact check (cheap part)
    init_bad = None
    if m0 > 0:
        Mcap = min(m0-1, cap)
        if Mcap >= 0:
            N, D = gkn_ND(k, n)
            c0 = series_div_frac(N, D, Mcap)
            mn = min(c0)
            if mn < 0:
                init_bad = (c0.index(mn), mn)
    if init_bad:
        return {"k":k,"n":n,"status":"counterexample-initial", "m":init_bad[0], "val":str(init_bad[1])}
    if lb > 0:
        return {"k":k,"n":n,"status":"proved", "lb":str(lb), "m0":m0}
    # search for negative in tail over residues
    L = 1
    for c in fs: L = L*c//gcd(L, c)
    rnd = random.Random(seed*1000003+k*97+n)
    best = None
    if L <= 3000000:
        for m in range(L):
            t = C + sum(fs[c][m % c] for c in fs)
            if best is None or t < best: best = t
            if t < 0:
                return {"k":k,"n":n,"status":"counterexample-tail", "m":m0+m, "val":str(t), "res":m}
        return {"k":k,"n":n,"status":"proved-tail-exhaustive", "min":str(best), "m0":m0, "L":L}
    for _ in range(samples):
        m = rnd.randrange(L)
        t = C + sum(fs[c][m % c] for c in fs)
        if best is None or t < best: best = t
        if t < 0:
            return {"k":k,"n":n,"status":"counterexample-tail", "m":m0+m, "val":str(t), "res":m}
    return {"k":k,"n":n,"status":"inconclusive", "lb":str(lb), "best":str(best), "L":L, "m0":m0}

if __name__ == "__main__":
    t0 = time.time()
    results = {}
    bad = []
    inconcl = []
    for n in range(0, 61):
        for k in range(1, 201):
            r = analyze(k, n)
            st = r["status"]
            if st.startswith("counterexample") or st == "repeated-pole":
                bad.append(r); print("HIT:", r); sys.stdout.flush()
            elif st == "inconclusive":
                inconcl.append(r)
        print(f"n={n} done ({time.time()-t0:.0f}s), hits={len(bad)}, inconclusive={len(inconcl)}"); sys.stdout.flush()
    import json
    json.dump({"hits":bad, "inconclusive":inconcl[:50], "n_inconclusive_total":len(inconcl)},
              open("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks/scan_results.json","w"), indent=1)
    print("DONE. hits:", len(bad), "inconclusive:", len(inconcl))

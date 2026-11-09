# run_target.py -- certify open configurations of a Level-2 target with gen_hd.
#   python3 -I run_target.py <target> [config filter: "S" or "S:all"] [max_k]
# For every open configuration (S_low, far multiset) (list taken from the L2c report; E's
# independent enumeration agrees), compute the slice decomposition (own implementation), then:
#   k = #free far coefficients <= 2 (dim <= 3): one certificate per DISTINCT ORDERING of the
#       free coefficients, domain "ordered" (checked by the untouched indep/checknd.py and by checkhd)
#   k >= 3 (dim >= 4): one certificate, domain "unordered" (all orderings), checked by checkhd.py
# A configuration counts as CLOSED only if every slice and every ordering is certified.
import sys, os, json, math, time, itertools
import multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import vp
import gen_hd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "..")
SUP = json.load(open(os.path.join(HERE, os.environ.get("HD_SUPPLY", "supply_B.json"))))   # default unchanged

def slices(K0, far):
    """exhaustive split so that on every emitted slice all free positions are >= t0'+1 (t0' = v2(K')).
    state: (K, free coefficient tuple, floors).  Fixed digits are folded into K."""
    out = set()
    stack = [(K0, tuple(sorted(far)), (3,) * len(far))]
    seen = set()
    while stack:
        st = stack.pop()
        if st in seen: continue
        seen.add(st)
        K, free, fl = st
        t0 = vp(K, 2)
        low = [i for i in range(len(free)) if fl[i] <= t0]
        if not low:
            out.add((K, free)); continue
        i = low[0]; A = free[i]
        rest = free[:i] + free[i + 1:]; rfl = fl[:i] + fl[i + 1:]
        for q in range(fl[i], t0 + 1):
            stack.append((K + A * 10 ** q, rest, rfl))
        stack.append((K, free, fl[:i] + (t0 + 1,) + fl[i + 1:]))
        if len(seen) > 2_000_000: raise RuntimeError("slice explosion")
    return sorted(out)

SCHED = {1: [[], [2, 3, 2, 3, 2]], 2: [[], [2, 3, 2, 3]], 3: [[2, 3, 2, 3], [2, 3, 2, 5, 3, 2, 7], []],
         4: [[2, 3, 2, 5, 3, 2, 7], [2, 3, 7, 2, 3, 2, 2, 3, 5], [2, 3, 7, 3, 2, 2, 2, 3, 5]],
         5: [[2, 3, 7, 3, 2, 2, 2, 3, 5], [2, 3, 7, 2, 3, 2, 2, 3, 5]]}

def certify(job):
    """job = (tag, coefs, K, qmin, ordered, workers, fn) -> (tag, status, info, sols)"""
    tag, coefs, K, qmin, ordered, workers, fn = job
    dim = len(coefs) + 1
    last = None
    for sched in SCHED.get(dim, SCHED[5]):
        for maxp in ((2 * 10 ** 7, 10 ** 12) if ordered else (10 ** 12,)):
            G = gen_hd.Gen(coefs, K, qmin, SUP, ordered, maxp=maxp)
            t = time.time()
            try:
                nodes, info, st = gen_hd.run(G, sched, workers=workers,
                                             budget_s=300 if dim <= 3 else 1000)
            except RecursionError:
                nodes, info, st = None, [], "recursion"
            last = (sched, maxp, st, info[-3:])
            if nodes is not None:
                gen_hd.write_cert(fn, G, nodes, {"sched": sched, "maxp": maxp})
                return tag, "closed", {"sched": sched, "maxp": maxp, "nodes": len(nodes),
                                       "secs": round(time.time() - t, 1)}, gen_hd.solutions(nodes)
    return tag, "OPEN", {"last": str(last)}, []

def orderings(coefs):
    return sorted(set(itertools.permutations(coefs)))

def main():
    t = int(sys.argv[1])
    flt = sys.argv[2] if len(sys.argv) > 2 and sys.argv[2] != "-" else None
    maxk = int(sys.argv[3]) if len(sys.argv) > 3 else 99
    sol_json = json.load(open(os.path.join(ROOT, "verification", "glm", "L2c", f"solve_t{t}.json")))
    opens = [(tuple(ms), S) for ms, S in sol_json["open"]]
    # far multiset of each open configuration
    cfgs = []
    for ms, S in opens:
        for mrep in sol_json["multisets"]:
            if tuple(mrep["multiset"]) != ms: continue
            for c in mrep["configs"]:
                if c["S_low"] == S: cfgs.append((ms, S, tuple(sorted(c["far"]))))
    if flt: cfgs = [c for c in cfgs if str(c[1]) in flt.split(",")]
    base = os.environ.get("HD_OUT", HERE)          # default unchanged; HD_OUT isolates parallel runs
    outdir = os.path.join(base, "certs", f"t{t}"); os.makedirs(outdir, exist_ok=True)
    resfn = os.path.join(base, f"results_t{t}.json")
    results = json.load(open(resfn)) if os.path.exists(resfn) else {}
    for ms, S, far in cfgs:
        key = f"{S}|{','.join(map(str, far))}"
        if key in results and results[key]["status"] == "CLOSED": continue
        K0 = 9 * S - 1
        assert K0 % 5, "K = 0 mod 5 would force 5 | n"
        try: sl = slices(K0, far)
        except RuntimeError:
            results[key] = {"multiset": list(ms), "S_low": S, "far": list(far), "status": "OPEN (slice explosion)"}
            continue
        kmax = max(len(f) for _, f in sl)
        if kmax > maxk:
            results[key] = {"multiset": list(ms), "S_low": S, "far": list(far), "status": f"SKIPPED (k={kmax})",
                            "slices": len(sl)}
            continue
        print(f"== t={t} S={S} far={far} slices={len(sl)} kmax={kmax}", file=sys.stderr, flush=True)
        jobs = []
        for K2, free in sl:
            t02 = vp(K2, 2)
            qmin = max(3, t02 + 1) if free else t02 + 1
            if len(free) <= 2:
                for od in orderings(free):
                    fn = os.path.join(outdir, f"c_S{S}_K{K2}_o{'_'.join(map(str, od)) or 'none'}.jsonl")
                    jobs.append(((K2, od), list(od), K2, qmin, True, 1, fn))
            else:
                fn = os.path.join(outdir, f"c_S{S}_K{K2}_u{'_'.join(map(str, free))}.jsonl")
                jobs.append(((K2, free), list(free), K2, qmin, False, 30, fn))
        low = [j for j in jobs if j[4]]; high = [j for j in jobs if not j[4]]
        recs = []
        with mp.get_context("fork").Pool(30) as pool:
            recs += pool.map(certify, low, chunksize=1)
        for j in high: recs.append(certify(j))
        st = "CLOSED" if all(r[1] == "closed" for r in recs) else "OPEN"
        sols = sorted({(r[0][0], tuple(r[0][1]), tuple(s)) for r in recs for s in r[3]})
        results[key] = {"multiset": list(ms), "S_low": S, "far": list(far), "status": st,
                        "slices": len(sl), "certs": len(jobs),
                        "jobs": [{"K": r[0][0], "coefs": list(r[0][1]), "status": r[1], "info": r[2]} for r in recs],
                        "sz_solutions": [[k, list(c), list(s)] for k, c, s in sols]}
        print(f"   -> {st}  ({sum(1 for r in recs if r[1]=='closed')}/{len(recs)} certs)", file=sys.stderr, flush=True)
        json.dump(results, open(resfn, "w"), indent=1)
    json.dump(results, open(resfn, "w"), indent=1)

if __name__ == "__main__":
    main()

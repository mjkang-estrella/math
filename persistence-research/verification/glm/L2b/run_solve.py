# L2b driver: solve my 9 stock targets (5 !| t) with the verbatim L2c pipeline copy.
# Caches the shared brute bucket (2^i 3^j 7^k <= 10^300, bucketed by Pi) so reruns
# are cheap.  Usage: python3 -I run_solve.py [t ...]   (default: all 9)
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pipeline as P

HERE = os.path.dirname(os.path.abspath(__file__))
ALL = [12, 14, 16, 18, 21, 24, 32, 42, 81]
ts = [int(a) for a in sys.argv[1:]] or ALL
cache = os.path.join(HERE, "bucket9.json")
need = [t for t in ts if t not in (15,)]
if os.path.exists(cache):
    bucket = {int(t): [int(x) for x in v] for t, v in json.load(open(cache)).items()}
    miss = [t for t in need if t not in bucket]
    if miss:
        b = P.brute_bucket(miss, P.BRUTE_B)
        bucket.update(b)
        json.dump({str(t): sorted(v) for t, v in bucket.items()}, open(cache, "w"))
else:
    bucket = P.brute_bucket(need, P.BRUTE_B)
    json.dump({str(t): sorted(v) for t, v in bucket.items()}, open(cache, "w"))
for t in ts:
    t0 = time.time()
    rep = P.solve_target(t, bucket[t])
    print(f"== target {t} ({time.time()-t0:.0f}s): {len(rep['members'])} members: {rep['members']}")
    print(f"   brute(L<={P.BRUTE_B})={rep['brute_count']} brute_only={rep['brute_only']} gaps={rep['coverage_gaps']}")
    print(f"   open configs: {len(rep['open'])}: {rep['open'][:12]}")
    json.dump({"target": t, "members": rep["members"], "cert_members": rep["cert_members"],
               "brute_count": rep["brute_count"], "brute_only": rep["brute_only"],
               "coverage_gaps": rep["coverage_gaps"],
               "open": [[list(o[0]), o[1]] for o in rep["open"]],
               "multisets": rep["multisets"]},
              open(os.path.join(HERE, f"solve_t{t}.json"), "w"), indent=1)

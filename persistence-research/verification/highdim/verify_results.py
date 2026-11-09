# verify_results.py -- re-derive, for every CLOSED configuration in a results file, the full list of
# certificate files it needs (all slices; every distinct ordering for k <= 2, one unordered cert for
# k >= 3), confirm each exists, run the checkers, and report per-configuration verdicts.
#   python3 -I verify_results.py <results.json> <certdir> <logfile> [parallel=24]
# checknd.py (unchanged, Agent A) on every ordered cert; checkhd.py on every cert.
import sys, os, json, itertools, subprocess, hashlib, concurrent.futures as cf
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import vp
import run_target

HERE = os.path.dirname(os.path.abspath(__file__))
IND = os.path.join(HERE, "..", "indep")
res = json.load(open(sys.argv[1])); cdir = sys.argv[2]; logf = sys.argv[3]
PAR = int(sys.argv[4]) if len(sys.argv) > 4 else 24
need = {}
for key, v in res.items():
    if v["status"] != "CLOSED": continue
    S = v["S_low"]; files = []
    for K2, free in run_target.slices(9 * S - 1, tuple(v["far"])):
        if len(free) <= 2:
            for od in sorted(set(itertools.permutations(free))):
                files.append(os.path.join(cdir, f"c_S{S}_K{K2}_o{'_'.join(map(str, od)) or 'none'}.jsonl"))
        else:
            files.append(os.path.join(cdir, f"c_S{S}_K{K2}_u{'_'.join(map(str, free))}.jsonl"))
    need[key] = files
allf = sorted({f for fs in need.values() for f in fs})
missing = [f for f in allf if not os.path.exists(f)]
print(f"{len(need)} closed configs need {len(allf)} certificate files; missing {len(missing)}", flush=True)

def run(cmd):
    r = subprocess.run(["bash", "-c", "ulimit -v 4000000; " + cmd], capture_output=True, text=True)
    out = r.stdout + r.stderr
    return "PASS" if "RESULT: PASS" in out else "FAIL"

def check(f):
    dim = json.loads(open(f).readline())["dim"]
    h = hashlib.sha256(open(f, "rb").read()).hexdigest()[:16]
    out = {"file": os.path.basename(f), "sha": h, "dim": dim}
    out["hd"] = run(f"python3 -I {HERE}/checkhd.py {f} {12 if dim >= 4 else 40} {1 if dim <= 3 else 30}")
    if "_o" in os.path.basename(f):
        out["nd"] = run(f"python3 -I {IND}/checknd.py {f} 40")
    return out

present = [f for f in allf if os.path.exists(f)]
small = [f for f in present if json.loads(open(f).readline())["dim"] <= 3]
big = [f for f in present if f not in set(small)]
results = {}
with cf.ThreadPoolExecutor(PAR) as ex:
    for i, o in enumerate(ex.map(check, small)):
        results[o["file"]] = o
        if i % 500 == 0: print(f"  small {i}/{len(small)}", flush=True)
for f in big:
    o = check(f); results[o["file"]] = o
    print(f"  big {o['file']} hd={o['hd']}", flush=True)
json.dump(results, open(logf, "w"), indent=0)
bad = {k: [os.path.basename(f) for f in fs if not os.path.exists(f) or results[os.path.basename(f)]["hd"] != "PASS"
           or results[os.path.basename(f)].get("nd", "PASS") != "PASS"] for k, fs in need.items()}
nbad = sum(1 for v in bad.values() if v)
print(f"checkhd PASS {sum(1 for o in results.values() if o['hd']=='PASS')}/{len(results)}; "
      f"checknd PASS {sum(1 for o in results.values() if o.get('nd')=='PASS')}/{sum(1 for o in results.values() if 'nd' in o)}")
print(f"configurations fully verified: {len(need)-nbad}/{len(need)}")
for k, v in bad.items():
    if v: print("  NOT VERIFIED", k, v[:5])

import json, hashlib, os, sys
lane = os.path.dirname(os.path.abspath(__file__))
out = {"lane_checks": [], "fail": []}
def chk(name, ok, detail=""):
    out["lane_checks"].append({"check": name, "ok": bool(ok), "detail": detail})
    if not ok: out["fail"].append(name)

# 1. input bindings still match registered hashes
fn = json.load(open("frozen/freeze-note.json"))
for key, b in fn["bindings"].items():
    p = os.path.normpath(os.path.join(lane, b["path"]))
    h = hashlib.sha256(open(p, "rb").read()).hexdigest()
    chk("binding_" + key, h == b["sha256"], h[:16])

# 2. JSON files parse; manifest excludes itself and receipt by exact relative name
for f in ("frozen/freeze-note.json", "disposition.json", "MANIFEST.json", "checks/run_output.json"):
    json.load(open(f))
man = json.load(open("MANIFEST.json"))
chk("manifest_excludes", "MANIFEST.json" in man["excluded_from_manifest"] and "verification-receipt.json" in man["excluded_from_manifest"])
chk("manifest_files_exist", all(os.path.exists(os.path.join(lane, f["path"])) for f in man["files"]))

# 3. rerun the exact verification fresh and compare to stored output
sys.path.insert(0, "checks")
import subprocess, tempfile
code = open("checks/verify_371202_exact.py").read()
r = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=200)
fresh = json.loads(r.stdout)
stored = json.load(open("checks/run_output.json"))
chk("rerun_A_zero_mismatch", fresh["A_criterion_mismatch_count"] == 0)
chk("rerun_B_all_match", all(x["match"] for x in fresh["B_counts"]))
chk("rerun_C_limit", fresh["C_limit_is_5_over_24"] is True and fresh["C_limit_errors"][-1]["abs_err_lt"] < 1e-6)
chk("rerun_matches_stored", fresh == stored)

# 4. independent spot re-check of the decisive identity at N=300: count == 5*300^2/6 == 75000
N = 300
c = sum(1 for x in range(-N, N+1) for y in range(-N, N+1)
        if ((lambda a,b: (a>0 and (b>3*a or b<-2*a)) or (a<0 and (b<3*a or b>-2*a)) or (a==0 and b!=0))(*((x,y) if x>=0 else (-x,-y)))))
chk("N300_count_75000", c == 75000, str(c))

print(json.dumps(out, indent=1))
sys.exit(1 if out["fail"] else 0)

# Validate every cert_t*.jsonl in L2b with Agent A's INDEPENDENT checker
# verification/indep/checknd.py (shares no code with the generator).
import glob, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
INDEP = os.path.join(HERE, "..", "..", "indep", "checknd.py")
BRUTE = sys.argv[1] if len(sys.argv) > 1 else "60"
npass = nfail = 0
fails = []
for fn in sorted(glob.glob(os.path.join(HERE, "cert_t*.jsonl"))):
    r = subprocess.run([sys.executable, "-I", INDEP, fn, BRUTE],
                       capture_output=True, text=True, timeout=600)
    ok = "RESULT: PASS" in r.stdout
    if ok: npass += 1
    else:
        nfail += 1
        fails.append((os.path.basename(fn), r.stdout[-500:], r.stderr[-300:]))
    print(("PASS " if ok else "FAIL ") + os.path.basename(fn), flush=True)
print(f"\nPASS={npass} FAIL={nfail}")
for f, o, e in fails:
    print("----", f); print(o); print(e)

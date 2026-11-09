# tamper.py -- positive controls and tamper tests for checkhd.py (and checknd.py where applicable).
# Builds control certificates with known solutions, including one whose solution has the far
# coefficients in NON-ascending position order (the ordering issue of REPORT_E), then mutates
# certificates and checks the verdicts.
import sys, os, json, subprocess, random, copy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_hd

HERE = os.path.dirname(os.path.abspath(__file__))
SUP = json.load(open(os.path.join(HERE, "supply_B.json")))
CD = os.path.join(HERE, "certs", "controls"); os.makedirs(CD, exist_ok=True)

def make(fn, coefs, K, qmin, ordered, sched):
    G = gen_hd.Gen(coefs, K, qmin, SUP, ordered)
    nodes, info, st = gen_hd.run(G, sched, workers=30)
    assert nodes is not None, st
    gen_hd.write_cert(fn, G, nodes, {"control": True})
    return gen_hd.solutions(nodes)

def check(fn, which="hd", brute=None):
    if which == "hd":
        cmd = ["python3", "-I", os.path.join(HERE, "checkhd.py"), fn] + ([str(brute)] if brute else [])
    else:
        cmd = ["python3", "-I", os.path.join(HERE, "..", "indep", "checknd.py"), fn] + ([str(brute)] if brute else [])
    r = subprocess.run(["bash", "-c", "ulimit -v 4000000; " + " ".join(cmd)], capture_output=True, text=True)
    out = r.stdout + r.stderr
    return ("PASS" if "RESULT: PASS" in out else "FAIL"), out

def load(fn): return [json.loads(l) for l in open(fn) if l.strip()]
def save(fn, recs):
    with open(fn, "w") as fo:
        for r in recs: fo.write(json.dumps(r) + "\n")

results = []
def expect(name, fn, want, which="hd", brute=None):
    got, out = check(fn, which, brute)
    ok = got == want
    results.append((name, want, got, ok))
    print(f"{'OK ' if ok else 'BAD'} {name}: expected {want}, got {got}")
    if not ok: print(out[-1500:])

# --- control 1: dim 4, coefs [9,27,54], solution with 9 at the HIGHEST position (unordered only)
X0 = 10 ** 6 + 9 * 10 ** 5 + 27 * 10 ** 4 + 54 * 10 ** 3
N = 3 ** 7 * 7 ** 4; K1 = N - X0
assert K1 > 0 and K1 % 2 == 1 and K1 % 5
c1 = os.path.join(CD, "ctrl_u_9_27_54.jsonl")
s1 = make(c1, [9, 27, 54], K1, 3, False, [2, 3, 2, 5, 3, 2, 7])
print("control 1 solutions:", s1)
assert (6, 5, 4, 3) in s1
expect("ctrl1 unordered positive control", c1, "PASS")
# same tree, claimed in ordered domain: the sz leaf lists a point outside the ordered domain -> FAIL
recs = load(c1); recs[0]["domain"] = "ordered"; t = c1 + ".ordered"; save(t, recs)
expect("ctrl1 relabelled ordered (sol outside ordered domain)", t, "FAIL")
# delete the solution from its sz leaf -> FAIL (both sz recomputation and brute box)
recs = load(c1)
for r in recs[1:]:
    if r.get("k") == "l" and "sz" in r["x"] and [6, 5, 4, 3] in r["x"]["sol"]:
        r["x"]["sol"].remove([6, 5, 4, 3])
t = c1 + ".delsol"; save(t, recs)
expect("ctrl1 deleted unordered solution", t, "FAIL")
# replace that sz leaf by a prime kill -> FAIL
recs = load(c1)
for r in recs[1:]:
    if r.get("k") == "l" and "sz" in r["x"] and [6, 5, 4, 3] in r["x"]["sol"]:
        r["x"] = {"prime": 37}
t = c1 + ".szprime"; save(t, recs)
expect("ctrl1 solution leaf replaced by prime kill", t, "FAIL")
# ordered generation of the same equation: the solution is NOT in the ordered domain, cert passes
# under BOTH checkers; this is exactly why every ordering must be certified separately in ordered mode
c1o = os.path.join(CD, "ctrl_o_9_27_54.jsonl")
s1o = make(c1o, [9, 27, 54], K1, 3, True, [2, 3, 2, 5, 3, 2, 7])
print("control 1 ordered solutions:", s1o)
expect("ctrl1 ordered-domain cert (solution invisible, as expected)", c1o, "PASS")
# the ordering that contains it: coefs [54,27,9] ordered
c1p = os.path.join(CD, "ctrl_o_54_27_9.jsonl")
s1p = make(c1p, [54, 27, 9], K1, 3, True, [2, 3, 2, 5, 3, 2, 7])
print("control 1 permuted-ordered solutions:", s1p)
assert (6, 3, 4, 5) in s1p
expect("ctrl1 permuted ordering positive control", c1p, "PASS")

# --- control 2: dim 3 (checknd-compatible), known solution, both checkers
X0 = 10 ** 6 + 9 * 10 ** 3 + 18 * 10 ** 4
N = 3 ** 6 * 7 ** 4; K2 = N - X0
assert K2 > 0 and K2 % 5
from hnt import vp
q2 = max(3, vp(K2, 2) + 1)
c2 = os.path.join(CD, "ctrl_o_9_18.jsonl")
s2 = make(c2, [9, 18], K2, q2, True, [])
print("control 2 solutions:", s2, "qmin", q2)
expect("ctrl2 dim3 positive control (checkhd)", c2, "PASS")
expect("ctrl2 dim3 positive control (checknd)", c2, "PASS", which="nd")

# --- structural tampers on a real certificate (dim 4 slice K=5489) and on control 1
base = os.path.join(HERE, "certs", "t112")
real = [os.path.join(base, f) for f in sorted(os.listdir(base)) if "_u" in f] if os.path.isdir(base) else []
targets = [c1] + real[:1]
random.seed(1)
for fn in targets:
    recs = load(fn)
    inter = [i for i, r in enumerate(recs) if i and r.get("k") == "i" and r["c"]]
    # (a) drop a child from a parent's child list
    rr = copy.deepcopy(recs); i = random.choice(inter); c = rr[i]["c"].pop()
    kids = {x["id"]: x.get("c", []) for x in rr[1:]}; drop = set(); st = [c]
    while st:
        u = st.pop(); drop.add(u); st += kids.get(u, [])
    rr = [rr[0]] + [x for x in rr[1:] if x["id"] not in drop]     # remove the whole subtree
    t = fn + ".dropchild"; save(t, rr)
    expect(f"{os.path.basename(fn)} dropped child", t, "FAIL")
    # (b) bogus rest prime list
    rr = copy.deepcopy(recs)
    cand = [i for i in inter if rr[i]["rest"]]
    i = random.choice(cand); rr[i]["rest"] = [11]
    t = fn + ".badrest"; save(t, rr)
    expect(f"{os.path.basename(fn)} bogus rest prime", t, "FAIL")
    # (c) perturb a child residue
    rr = copy.deepcopy(recs); i = random.choice(inter); cid = rr[i]["c"][0]
    j = next(k for k, x in enumerate(rr) if x.get("id") == cid)
    rr[j]["r"][0] += rr[i]["m"]          # same parent class, different lift
    t = fn + ".perturb"; save(t, rr)
    expect(f"{os.path.basename(fn)} perturbed child residue", t, "FAIL")
    # (d) wrong sz exponent / wrong prime leaf
    rr = copy.deepcopy(recs)
    leaves = [k for k, x in enumerate(rr) if k and x.get("k") == "l"]
    if leaves:
        k = random.choice(leaves)
        if "sz" in rr[k]["x"]: rr[k]["x"]["sz"][0] += 1
        else: rr[k]["x"]["prime"] = 11
        t = fn + ".leaf"; save(t, rr)
        expect(f"{os.path.basename(fn)} corrupted leaf", t, "FAIL")
    # (e) partial root
    rr = copy.deepcopy(recs); rr[0]["root"] = {"r": [1] * rr[0]["dim"], "m": 2}
    t = fn + ".root"; save(t, rr)
    expect(f"{os.path.basename(fn)} partial root", t, "FAIL")
    # (f) changed K
    rr = copy.deepcopy(recs); rr[0]["K"] += 2 ** (rr[0]["qmin"] + 1) * 9
    t = fn + ".K"; save(t, rr)
    expect(f"{os.path.basename(fn)} changed K", t, "FAIL")

print(f"\n{sum(1 for r in results if r[3])}/{len(results)} tamper/control expectations met")
json.dump(results, open(os.path.join(HERE, "logs", "tamper_results.json"), "w"), indent=1)

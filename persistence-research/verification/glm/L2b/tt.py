import json, subprocess, sys, shutil, os
HERE = "/home/mj-kang/Documents/Dev/math/persistence-research/verification/glm/L2b"
CK = HERE + "/checknd5.py"
def run(path):
    r = subprocess.run([sys.executable, "-I", CK, path, "60"], capture_output=True, text=True)
    out = r.stdout + r.stderr
    return "RESULT: PASS" in out, out.strip().splitlines()[-3:]

# 1. regression: checknd5 on stock (five absent) certs == checknd behaviour
for f in ["cert_t12_S11_K98_c18.jsonl", "cert_t32_S1_K8_c27_27.jsonl", "cert_t42_S1_K8_c18_54.jsonl"]:
    ok, tail = run(os.path.join(HERE, f))
    print("regression", f, "PASS" if ok else "FAIL", tail[0] if tail else "")

src = HERE + "/cert_t15_S24_K215_cnone.jsonl"
lines = open(src).read().splitlines()

# 2. tamper: flip five flag off (K % 5 == 0 must then be rejected)
p = "/tmp/tamper/a.jsonl"
d = json.loads(lines[0]); d["five"] = False
open(p, "w").write(json.dumps(d) + "\n" + "\n".join(lines[1:]))
ok, tail = run(p); print("tamper five->false:", "REJECTED" if not ok else "ACCEPTED (BAD!)", tail)

# 3. tamper: delete one claimed sz solution
p = "/tmp/tamper/b.jsonl"
out = []
for l in lines:
    d = json.loads(l)
    if d.get("k") == "l" and "sz" in d.get("x", {}) and d["x"]["sol"]:
        d["x"]["sol"] = d["x"]["sol"][1:]
    out.append(json.dumps(d))
open(p, "w").write("\n".join(out))
ok, tail = run(p); print("tamper drop sol:", "REJECTED" if not ok else "ACCEPTED (BAD!)", tail)

# 4. tamper: K -> K + 5 (still 5 | K, changes the equation)
p = "/tmp/tamper/c.jsonl"
out = []
for l in lines:
    d = json.loads(l)
    if d.get("k") == "meta": d["K"] += 5
    out.append(json.dumps(d))
open(p, "w").write("\n".join(out))
ok, tail = run(p); print("tamper K+5:", "REJECTED" if not ok else "ACCEPTED (BAD!)", tail)

# 5. positive control: the five cert itself passes
ok, tail = run(src); print("control five cert:", "PASS" if ok else "FAIL")

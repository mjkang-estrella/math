import json, subprocess, sys, os
HERE = "/home/mj-kang/Documents/Dev/math/persistence-research/verification/glm/L2b"
def run(ck, path):
    r = subprocess.run([sys.executable, "-I", ck, path, "60"], capture_output=True, text=True)
    return "RESULT: PASS" in r.stdout, (r.stdout + r.stderr).strip().splitlines()[-2:]

# A. stock checker on five certs: must NOT pass (5-handling is load-bearing)
for f in ["cert_t15_S204_K1835_cnone.jsonl", "cert_t15_S24_K215_cnone.jsonl", "cert_t15_S4_K35_c18.jsonl"]:
    ok, tail = run(HERE + "/../../indep/checknd.py", os.path.join(HERE, f))
    print("stock-checker on", f, "->", "PASS (BAD!)" if ok else "rejected", tail)

# B. rest-prime tamper on the dim-2 five cert: swap a rest prime
src = HERE + "/cert_t15_S4_K35_c18.jsonl"
lines = open(src).read().splitlines()
out, done = [], False
for l in lines:
    d = json.loads(l)
    if not done and d.get("k") == "i" and d.get("rest"):
        d["rest"] = [p + 2 for p in d["rest"]]   # wrong primes
        done = True
    out.append(json.dumps(d))
p = "/tmp/tamper/d.jsonl"; open(p, "w").write("\n".join(out))
ok, tail = run(HERE + "/checknd5.py", p)
print("tamper rest-prime:", "REJECTED" if not ok else "ACCEPTED (BAD!)", tail)

# C. five=true on a stock cert (K % 5 != 0) -> must be rejected
src2 = HERE + "/cert_t12_S11_K98_c18.jsonl"
lines = open(src2).read().splitlines()
d = json.loads(lines[0]); d["five"] = True
open("/tmp/tamper/e.jsonl", "w").write(json.dumps(d) + "\n" + "\n".join(lines[1:]))
ok, tail = run(HERE + "/checknd5.py", "/tmp/tamper/e.jsonl")
print("tamper five->true on stock:", "REJECTED" if not ok else "ACCEPTED (BAD!)", tail)

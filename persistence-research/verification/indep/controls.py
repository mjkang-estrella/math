# Positive 3-D control + tamper tests for checknd.py
import json, subprocess, copy, sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); V = os.path.dirname(HERE)
def sh(cmd):
    r = subprocess.run(['bash', '-c', 'ulimit -v 1500000; ' + cmd], capture_output=True, text=True, cwd=V)
    return r.stdout + r.stderr
# --- 3-D positive control: find K with a known solution
best = None
L, q1, q2 = 6, 3, 4
base = 10 ** L + 9 * 10 ** q1 + 9 * 10 ** q2
cands = sorted((3 ** a * 7 ** w - base, a, w) for a in range(2, 20) for w in range(0, 9) if 3 ** a * 7 ** w > base)
for K, a, w in cands:
    if K % 2 == 1 and K % 5 != 0 and K < 10 ** 7: best = (L, q1, q2, a, w, K); break
print("3-D control equation:", best)
L, q1, q2, a, w, K = best
M = 2 * 3 ** max(a - 1, 1) * 7 ** w
out = sh(f"python3 -I indep/gen_nd.py indep/certs/ctrl3d.jsonl 3 9,9 {K} 3 {L},{q1},{q2} {M} | grep -E 'nodes=|solutions'; python3 -I indep/checknd.py indep/certs/ctrl3d.jsonl {L+3} | grep -E 'RESULT|claimed|brute'")
print(out)
assert "PASS" in out and f"({L}, {q1}, {q2})" in out
# --- tamper tests on a real certificate
def run_tamper(name, lines):
    p = f'/tmp/tamper_{name}.jsonl'
    open(p, 'w').write('\n'.join(json.dumps(x) for x in lines) + '\n')
    o = sh(f"python3 -I indep/checknd.py {p} 40 2>&1 | tail -4")
    ok = ('RESULT: FAIL' in o) or ('Error' in o)
    print(f"tamper[{name}] rejected: {ok}")
    assert ok, o
base = [json.loads(l) for l in open(os.path.join(V, 'indep/certs/my3d_K89.jsonl'))]
x = copy.deepcopy(base)
for n in x[1:]:
    if n['k'] == 'i' and n['rest']: n['rest'] = [101] if n['rest'] != [101] else [11]; break
run_tamper('wrong_rest_prime', x)
x = copy.deepcopy(base)
for n in x[1:]:
    if n['k'] == 'i' and n['c']: n['c'].pop(); break
run_tamper('dropped_child', x)
x = copy.deepcopy(base)
for n in x[1:]:
    if n['k'] == 'l': n['x']['sz'][0] += 1; break
run_tamper('wrong_sz_exponent', x)
# replace the true-solution sz leaf of the control by a prime kill: must be rejected
c = [json.loads(l) for l in open(os.path.join(V, 'indep/certs/ctrl3d.jsonl'))]
for n in c[1:]:
    if n['k'] == 'l': n['x'] = {'prime': 11}
run_tamper('kill_true_solution_class', c)
c = [json.loads(l) for l in open(os.path.join(V, 'indep/certs/ctrl3d.jsonl'))]
for n in c[1:]:
    if n['k'] == 'l': n['x']['sol'] = []
run_tamper('drop_recorded_solution', c)
print("all controls/tamper tests OK")

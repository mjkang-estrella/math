# Coverage bookkeeping: every Level-1 configuration (digit multiset + placement class) must be mapped to a proven closure.
import itertools, os, subprocess, sys, json
HERE = os.path.dirname(os.path.abspath(__file__)); V = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from nt import vp
mults = [(2, 2), (2, 3), (2, 4), (3, 3), (2, 2, 2)]
def parity_ok(K):
    if K % 5 == 0: return False
    for t in range(0, 12):
        for a in range(0, 8):
            for w in range(0, 8):
                v = 2 ** t * 3 ** a * 7 ** w
                if (v - K) % 8 == 0 and (v - K) % 5 == 0: return True
    return False
res = {}
for m in mults:
    k = len(m)
    for nlow in range(0, k + 1):
        for lowidx in itertools.combinations(range(k), nlow):
            for lowpos in itertools.permutations(range(3), nlow):
                S = sum((m[i] - 1) * 10 ** p for i, p in zip(lowidx, lowpos))
                far = tuple(sorted(m[i] - 1 for i in range(k) if i not in lowidx))
                res.setdefault((far, S), set()).add(m)
# also verify 9n = 10^L + sum A*10^q + K on random concrete numbers
import random
random.seed(7)
for _ in range(2000):
    L = random.randint(8, 30)
    m = random.choice(mults)
    pos = random.sample(range(L), len(m))
    n = (10 ** L - 1) // 9 + sum((d - 1) * 10 ** p for d, p in zip(m, pos))
    far = [(d - 1, p) for d, p in zip(m, pos) if p >= 3]
    Slow = sum((d - 1) * 10 ** p for d, p in zip(m, pos) if p < 3)
    assert 9 * n == 10 ** L + sum(9 * c * 10 ** p for c, p in far) + 9 * Slow - 1
print("formula 9n = 10^L + sum A*10^q + K (K=9*S_low-1, A=9c) verified on 2000 random numbers")
def check_cert(path, brute=30):
    if not os.path.exists(os.path.join(V, path)): return "MISSING"
    r = subprocess.run(['bash', '-c', f'ulimit -v 1500000; python3 -I indep/checknd.py {path} {brute}'], capture_output=True, text=True, cwd=V)
    return "PASS" if "RESULT: PASS" in r.stdout else "FAIL"
rows = []
def one_d(K, label):
    t = vp(K, 2); st = check_cert(f"indep/certs/my1d_K{K}.jsonl", 200)
    return f"1-D K={K} (domain L>={t+1}; L<={t} by brute force) {st}"
bad = 0
for (far, S), ms in sorted(res.items(), key=lambda kv: (len(kv[0][0]), kv[0][0], kv[0][1])):
    K = 9 * S - 1
    if not far:
        if S == 0: continue
        desc = "ALL-LOW: " + one_d(K, "")
    elif S == 0:
        desc = "(H) all non-1 digits at positions >=3: mod 8/mod 5 contradiction" + (" [parity check agrees]" if not parity_ok(K) else " [PARITY CHECK DISAGREES]")
        bad += parity_ok(K)
    elif not parity_ok(K):
        desc = "parity-dead (mod 8 / mod 5)"
    elif len(far) == 1:
        A = 9 * far[0]; t0 = vp(K, 2); qmin = max(3, t0 + 1)
        desc = f"ONE-FAR A={A}: 2-D cert my2d_A{A}_K{K} (q>={qmin}) " + check_cert(f"indep/certs/my2d_A{A}_K{K}.jsonl", 60)
        for q in range(3, qmin):
            Kq = K + A * 10 ** q; tq = vp(Kq, 2)
            desc += f" | slice q={q}: " + one_d(Kq, "")
    else:
        assert far == (1, 1)
        t0 = vp(K, 2); qmin = max(3, t0 + 1)
        desc = f"TWO-FAR {{2,2,2}}: 3-D cert my3d_K{K} (q1>={qmin}) " + check_cert(f"indep/certs/my3d_K{K}.jsonl", 40)
        for q1 in range(3, qmin):
            K1 = K + 9 * 10 ** q1; t1 = vp(K1, 2); qm2 = max(q1 + 1, t1 + 1)
            desc += f" | slice q1={q1}: 2-D A=9 K={K1} (q2>={qm2}) " + check_cert(f"indep/certs/my2d_A9_K{K1}.jsonl", 60)
            for q2 in range(q1 + 1, qm2):
                K2 = K1 + 9 * 10 ** q2
                desc += f" | slice q1={q1},q2={q2}: " + one_d(K2, "")
    if "FAIL" in desc or "MISSING" in desc: bad += 1
    print(f"far c={far} S_low={S} K={K} multisets={sorted(ms)}\n     -> {desc}")
print("UNCOVERED / FAILING configuration classes:", bad)

# Max |coeff| of (q;q)_m, incremental with checkpoint. usage: qmax.py MSTOP SECONDS
import sys, pickle, time, json, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
ck = D/'cache/qmax.pkl'; out = D/'outputs/qmax.json'
mstop, budget = int(sys.argv[1]), float(sys.argv[2])
if ck.exists():
    m, p, res = pickle.loads(ck.read_bytes())
else:
    m, p, res = 0, [1], {0: [1, 0]}
t = time.time()
while m < mstop and time.time() - t < budget:
    k = m + 1
    n = len(p)
    p = p + [0]*k
    for i in range(n + k - 1, k - 1, -1):
        p[i] -= p[i-k]
    m = k
    best = max(range(len(p)//2 + 1), key=lambda i: abs(p[i]))
    res[m] = [abs(p[best]), best]
ck.write_bytes(pickle.dumps((m, p, res)))
out.write_text(json.dumps(res))
print('reached m =', m, 'elapsed', time.time() - t)

# Exhaustive min slack for Conjecture 30 over RGS colourings (DP-based slack from cyclelocal.py).
import sys, json, time
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
import importlib.util
spec = importlib.util.spec_from_file_location('cl', sys.argv[0].rsplit('/', 1)[0] + '/cyclelocal.py')
src = open(spec.origin).read().split("l, h, seed, secs")[0]
ns = {}; exec(src, ns)
slack = ns['slack']
from itertools import product
l, h = int(sys.argv[1]), int(sys.argv[2])
def rgs(n, h):
    a = [0]*n
    def rec(i, mx):
        if i == n: yield tuple(a); return
        for v in range(min(mx+2, h)):
            a[i] = v; yield from rec(i+1, max(mx, v))
    yield from rec(1, 0)
t = time.time(); best = 99; ex = None; cnt = 0; tight = 0
for col in rgs(2*l, h):
    cnt += 1
    s = slack(list(col), l, h)[0]
    if s < best: best = s; ex = col; tight = 0
    if s == best: tight += 1
print(json.dumps({'l': l, 'h': h, 'colourings': cnt, 'min_slack': best, 'num_attaining': tight, 'example': ex, 'sec': round(time.time()-t, 1)}))

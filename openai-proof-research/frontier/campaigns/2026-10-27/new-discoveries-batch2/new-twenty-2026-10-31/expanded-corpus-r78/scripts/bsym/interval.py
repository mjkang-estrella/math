# Bridges W (b x r) whose columns are intervals of ones [lo_c, hi_c] (consecutive-ones => totally unimodular).
import sys, json, itertools, os
sys.path.insert(0, os.path.dirname(__file__))
from bridge import ok
def W_of(b, r, iv): return [[1 if iv[c][0] <= k <= iv[c][1] else 0 for c in range(r)] for k in range(b)]
B = int(sys.argv[1])
for b in range(2, B+1):
    for r in range(1, b):
        ivs = [(lo, hi) for lo in range(b) for hi in range(lo, b)]
        found = None; cnt = 0
        # DFS columns with partial pruning on (A): leading minor j uses columns 0..j-1
        def rec(cols):
            global found, cnt
            if found: return
            j = len(cols)
            if j:
                W = W_of(b, j, cols)
                from bridge import det
                if abs(det([W[i][:j] for i in range(j)])) != 1: return
            if j == r:
                if ok(W_of(b, r, cols), b, r): found = list(cols)
                return
            for iv in ivs:
                rec(cols + [iv])
                if found: return
        rec([])
        print(json.dumps({'b': b, 'r': r, 'intervals': found}), flush=True)

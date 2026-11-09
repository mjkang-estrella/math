import sys, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
from bridge import ok
def fam(name, b, r):
    W = []
    for k in range(b):
        if name == 'F2':
            if k < r: row = [1 if c <= k else 0 for c in range(r)]
            elif k >= b - r: i = k - (b - r); row = [1 if c >= i else 0 for c in range(r)]
            else: row = [1 if c == k % r else 0 for c in range(r)]
        elif name == 'F3':  # top unit (identity), middle periodic, bottom U
            if k >= b - r and k >= r: i = k - (b - r); row = [1 if c >= i else 0 for c in range(r)]
            else: row = [1 if c == k % r else 0 for c in range(r)]
        elif name == 'F4':  # periodic aligned to top; replace last row by all ones
            row = [1 if c == k % r else 0 for c in range(r)]
            if k == b - 1: row = [1]*r
        elif name == 'F5':  # periodic top-aligned; bottom rows: row k = sum of e_c for c >= (k-(b-r))  OR'd with periodic
            row = [1 if c == k % r else 0 for c in range(r)]
            if k >= b - r:
                i = k - (b - r); row = [1 if (c >= i or c == k % r) else 0 for c in range(r)]
        W.append(row)
    return W
res = {}
B = int(sys.argv[1])
for name in ['F2', 'F3', 'F4', 'F5']:
    fails = []
    for b in range(2, B+1):
        for r in range(1, b):
            if not ok(fam(name, b, r), b, r): fails.append((b, r))
    res[name] = {'fails': len(fails), 'first': fails[:12]}
print(json.dumps(res))

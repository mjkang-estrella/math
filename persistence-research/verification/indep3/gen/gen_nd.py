# My own sieve/certificate generator, dimension 2 or 3 (common modulus M).
# usage: python3 -I gen_nd.py out.jsonl dim "coef1[,coef2]" K qmin [root_r1,r2[,r3] root_M] [--pmax N] [--nmax n] [--mcap M] [--deep d]
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sievelib import Sieve
args = sys.argv[1:]
def opt(name, default):
    if name in args:
        i = args.index(name); v = int(args[i + 1]); del args[i:i + 2]; return v
    return default
DEEP = opt('--deep', 8); PMAX = opt('--pmax', 20000000); NMAX = opt('--nmax', 8); MCAP = opt('--mcap', 10 ** 13)
out, DIM, coefs, K, QMIN = args[0], int(args[1]), [int(x) for x in args[2].split(',') if x], int(args[3]), int(args[4])
if len(args) > 5: ROOT_R = tuple(int(x) for x in args[5].split(',')); ROOT_M = int(args[6])
else: ROOT_R, ROOT_M = (0,) * DIM, 1
S = Sieve(coefs, K, QMIN, pmax=PMAX, cache=os.environ.get('E_UNIV') or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'univ_%dM.json' % (PMAX // 10 ** 6)))
t0 = S.t0
nodes = []; unresolved = []

def evaluate(r, M, f):
    M2 = M * f; alive = []; used = []
    for r2 in S.lifts(r, M, M2):
        a, w = S.sig(r2, M2)
        p = S.kill_by(r2, M2, a, w)
        if p is None: alive.append((r2, a, w))
        elif p not in used: used.append(p)
    unres = sum(1 for (_, a, w) in alive if a[1] is None or w[1] is None)
    return M2, alive, used, unres

def process(r, M, parent, depth=0):
    nid = len(nodes)
    if nid % 500 == 0: print('progress nodes', nid, 'M', M, 'depth', depth, file=sys.stderr, flush=True)
    a, w = S.sig(r, M)
    if a[1] is not None and w[1] is not None:
        N = 2 ** t0 * 3 ** a[0] * 7 ** w[0]
        sols = sorted(s for s in S.in_domain_points(N) if all(v % M == x % M for v, x in zip(s, r)))
        nodes.append({"id": nid, "p": parent, "k": "l", "r": list(r), "m": M, "a": list(a), "w": list(w), "x": {"sz": [a[0], w[0]], "sol": [list(s) for s in sols]}})
        return nid
    if M > MCAP:
        nodes.append({"id": nid, "p": parent, "k": "u", "r": list(r), "m": M, "a": list(a), "w": list(w)})
        unresolved.append((r, M, a, w)); return nid
    cand = {f for f in range(2, NMAX + 1)}
    if a[1] is None: cand.add(3)
    if w[1] is None: cand.add(7)
    if depth >= DEEP:
        cand = set()
        if M % 2: cand.add(2)
        if a[1] is None: cand.add(3)
        if w[1] is None and M % 6 == 0: cand.add(7)
    best = None
    for f in sorted(cand):
        if f ** DIM > 3000 and f not in (3, 7): continue
        M2, alive, used, unres = evaluate(r, M, f)
        score = (unres, len(alive), 0 if ((f == 3 and a[1] is None) or (f == 7 and w[1] is None)) else 1, f)
        if best is None or score < best[0]: best = (score, f, M2, alive, used)
        if unres == 0 and len(alive) == 0: break
    _, f, M2, alive, used = best
    nodes.append({"id": nid, "p": parent, "k": "i", "r": [x % M for x in r], "m": M, "m2": M2, "c": [], "rest": used if len(alive) < f ** DIM else None})
    nodes[nid]["c"] = [process(r2, M2, nid, depth + 1) for (r2, a2, w2) in alive]
    return nid

sys.setrecursionlimit(10000)
process(ROOT_R, ROOT_M, -1)
meta = {"k": "meta", "dim": DIM, "coefs": coefs, "K": K, "qmin": QMIN, "root": {"r": list(ROOT_R), "m": ROOT_M}}
with open(out, 'w') as fo:
    fo.write(json.dumps(meta) + '\n')
    for n in nodes: fo.write(json.dumps(n) + '\n')
leaves = [n for n in nodes if n['k'] == 'l']
print(f"{out}: nodes={len(nodes)} sz-leaves={len(leaves)} unresolved={len(unresolved)} max M={max(n['m'] for n in nodes)}")
print("solutions:", sorted({tuple(s) for n in leaves for s in n['x']['sol']}))
if unresolved:
    for u in unresolved[:10]: print("UNRESOLVED", u)
    sys.exit(2)

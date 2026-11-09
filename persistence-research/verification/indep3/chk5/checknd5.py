# checknd5.py — L2b copy of Agent A's INDEPENDENT checker verification/indep/checknd.py
# with ONE documented extension for the target t = 15 = 3*5 (the only 5 | t target of
# part B).  Everything else is byte-identical to checknd.py.
#
# Extension ("five" mode, meta flag "five": true):
#   For t = 15 every solution n has digits {1,3,5} (one 3, one 5); n is odd and
#   v5(n) <= 1 (n would have to end in 25/75, impossible with digits {1,3,5}).
#   On the sieve domain (L >= 1, all far q >= qmin >= 3 >= 1) we have
#   X mod 5 = K mod 5, so per configuration:  5 | K  <=>  5 | X = 9n  <=>  5 | n,
#   and then X = 5 * 2^t0 3^a 7^w with the SAME a, w, t0 as the stock format
#   (v3, v7, v2 are untouched by the factor 5).  The sieve therefore solves
#   Y := X/5 = 2^t0 3^a 7^w, which is implemented by multiplying X mod m by 5^{-1}
#   (every modulus m is coprime to 5: m in {3^{j+2}, 7^{i+1}, primes p > 7}).
#   The checker mirrors exactly that: Xmod returns Y mod m in five mode, the sz
#   leaf value becomes N = 5 * 2^t0 3^a 7^w, and the brute box strips the 5.
#   Soundness of the 5^{-1} trick does not rely on any generator convention: it is
#   an exact integer identity on the whole domain, and K % 5 is checked against
#   the flag (five <=> 5 | K), so a five certificate can never certify a 5 !| K
#   equation or vice versa.
# usage: python3 -I checknd5.py cert.jsonl [brute_Lmax]
import sys, os, json, math, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import vp, order, lcm, isprime

path = sys.argv[1]
BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 60
raw = [json.loads(l) for l in open(path) if l.strip()]
meta = raw[0]; assert meta['k'] == 'meta'
nodes = {n['id']: n for n in raw[1:]}
assert len(nodes) == len(raw) - 1, "duplicate ids"
DIM, COEFS, K, QMIN = meta['dim'], meta['coefs'], meta['K'], meta['qmin']
assert len(COEFS) == DIM - 1 and DIM in (1, 2, 3)
FIVE = bool(meta.get('five', False))
ROOT_R, ROOT_M = tuple(meta['root']['r']), meta['root']['m']
t0 = vp(K, 2)
assert K > 0 and ((K % 5 == 0) == FIVE) and QMIN > t0
stats = collections.Counter(); problems = []
def bad(s): problems.append(s)

def Xmod(r, m):
    s = pow(10, r[0], m) + K
    for c, e in zip(COEFS, r[1:]): s += c * pow(10, e, m)
    if FIVE: s = s * pow(5, -1, m) % m   # Y = X/5; m coprime to 5 always
    return s % m

def sig(r, M):
    j = vp(M, 3); m3 = 3 ** (j + 2)
    assert pow(10, 3 ** j, m3) == 1
    x = Xmod(r, m3)
    a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
    if M % 6 == 0:
        i = vp(M, 7); m7 = 7 ** (i + 1)
        assert pow(10, 6 * 7 ** i, m7) == 1
        x = Xmod(r, m7)
        w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
    else: w = (0, None)
    return a, w

def lifts(r, M, M2):
    f = M2 // M
    for t in itertools.product(range(f), repeat=DIM):
        yield tuple((x % M) + k * M for x, k in zip(r, t))

def kill_prime(p, r, M):
    assert isprime(p) and p > 7
    d = order(10, p)
    if M % d:
        M2 = lcm(M, d)
        stats['lifted'] += (M2 // M) ** DIM
        return all(kill_prime(p, r2, M2) for r2 in lifts(r, M, M2))
    a, w = sig(r, M)
    T = Xmod([x % d for x in r], p) * pow(2, -t0, p) % p
    if T == 0: return True
    o3, o7 = order(3, p), order(7, p)
    x = T * pow(3, -a[0], p) * pow(7, -w[0], p) % p
    af, wf = a[1] is None, w[1] is None
    if af and wf: return pow(x, lcm(o3, o7), p) != 1
    if af: return pow(x, o3, p) != 1
    if wf: return pow(x, o7, p) != 1
    return x != 1

def in_domain_points(N):
    """all domain points (L,q1..) whose X equals N"""
    out = []
    D = len(str(N)) + 1
    if DIM == 1:
        for L in range(QMIN, D + 1):
            if 10 ** L + K == N: out.append((L,))
    elif DIM == 2:
        for L in range(2, D + 1):
            for q in range(QMIN, L):
                if 10 ** L + COEFS[0] * 10 ** q + K == N: out.append((L, q))
    else:
        for q2 in range(QMIN + 1, D + 1):
            for q1 in range(QMIN, q2):
                R = N - K - COEFS[0] * 10 ** q1 - COEFS[1] * 10 ** q2
                if R > 0:
                    s = str(R)
                    if s == '1' + '0' * (len(s) - 1):
                        L = len(s) - 1
                        if L > q2: out.append((L, q1, q2))
    return out

claimed = set()
visited = set()
def visit(i, r, M):
    assert i in nodes and i not in visited, ("bad/duplicate node", i); visited.add(i)
    nd = nodes[i]
    if nd['k'] == 'l':
        stats['leaves'] += 1
        a, w = sig(r, M); x = nd['x']
        if 'prime' in x:
            if kill_prime(x['prime'], r, M): stats['leaf_prime_ok'] += 1
            else: stats['leaf_prime_FAIL'] += 1; bad(f"leaf {i} r={r} M={M}: prime {x['prime']} fails (sig {a},{w})")
        elif 'sz' in x:
            if a[1] is None or w[1] is None: bad(f"leaf {i}: sz with non-exact signature {a},{w}"); return
            if list(x['sz']) != [a[0], w[0]]: bad(f"leaf {i}: sz exponents wrong"); return
            N = 2 ** t0 * 3 ** a[0] * 7 ** w[0]
            if FIVE: N *= 5
            sols = sorted(s for s in in_domain_points(N) if all(si % M == ri % M for si, ri in zip(s, r)))
            if sols != sorted(tuple(s) for s in x['sol']): bad(f"leaf {i}: sz solutions {sols} != declared {x['sol']}")
            else: stats['leaf_sz_ok'] += 1
            claimed.update(sols)
        else: bad(f"leaf {i}: unknown kill {x}")
        return
    ch = [nodes[c] for c in nd['c']]
    M2 = nd['m2']; assert M2 % M == 0 and M2 > M and all(c['m'] == M2 for c in ch)
    cres = [tuple(x % M2 for x in c['r']) for c in ch]
    assert len(set(cres)) == len(cres), f"dup children at {i}"
    for cr in cres: assert all(x % M == y % M for x, y in zip(cr, r)), f"child outside parent at {i}"
    cset = set(cres)
    for rr in lifts(r, M, M2):
        if rr in cset: continue
        rp = nd['rest']
        if rp is None: rp = []
        if isinstance(rp, int): rp = [rp]
        if not rp: bad(f"node {i}: lift {rr} mod {M2} neither child nor killed"); continue
        if any(kill_prime(p, rr, M2) for p in rp): stats['rest_ok'] += 1
        else: bad(f"node {i}: rest lift {rr} mod {M2} survives primes {rp}"); stats['rest_FAIL'] += 1
    for c, cr in zip(nd['c'], cres): visit(c, cr, M2)

roots = [i for i, n in nodes.items() if n['p'] == -1]
assert len(roots) == 1
visit(roots[0], ROOT_R, ROOT_M)
if len(visited) != len(nodes): bad("unreachable nodes")

def locate(x):
    i = roots[0]
    while True:
        nd = nodes[i]
        if nd['k'] == 'l': return i
        M2 = nd['m2']
        key = tuple(v % M2 for v in x)
        nxt = None
        for c in nd['c']:
            if tuple(v % M2 for v in nodes[c]['r']) == key: nxt = c; break
        if nxt is None: return None
        i = nxt

brute = []
npts = 0
def Xval(x):
    s = 10 ** x[0] + K
    for c, e in zip(COEFS, x[1:]): s += c * 10 ** e
    return s
if DIM == 1: pts = ((L,) for L in range(QMIN, BRUTE + 1))
elif DIM == 2: pts = ((L, q) for L in range(QMIN + 1, BRUTE + 1) for q in range(QMIN, L))
else: pts = ((L, q1, q2) for L in range(QMIN + 2, BRUTE + 1) for q2 in range(QMIN + 1, L) for q1 in range(QMIN, q2))
for x in pts:
    if not all(v % ROOT_M == r % ROOT_M for v, r in zip(x, ROOT_R)): continue
    npts += 1
    X = Xval(x)
    if X % (1 << t0) or ((X >> t0) & 1) == 0: continue
    Y = X >> t0
    if FIVE:
        if X % 5: continue          # five solutions have v5(X) = 1 exactly
        Y = (X // 5) >> t0
    for pr in (3, 7):
        while Y % pr == 0: Y //= pr
    if Y == 1:
        brute.append(x)
        li = locate(x)
        if li is None or 'sz' not in nodes[li]['x'] or list(x) not in [list(s) for s in nodes[li]['x']['sol']]:
            bad(f"brute solution {x} not recorded in an sz leaf")
print(f"{os.path.basename(path)}: dim={DIM} coefs={COEFS} K={K} qmin={QMIN} root=({list(ROOT_R)} mod {ROOT_M}) nodes={len(nodes)}")
print("   stats:", dict(stats))
print(f"   claimed solutions: {sorted(claimed)}")
print(f"   brute-force solutions in box L<={BRUTE} ({npts} pts): {brute}")
if set(brute) != {s for s in claimed if s[0] <= BRUTE}: bad("claimed vs brute mismatch")
if problems:
    print("   RESULT: FAIL"); [print("     -", p) for p in problems[:10]]; sys.exit(1)
print("   RESULT: PASS")

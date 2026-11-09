# checkhd.py -- checker for `nd` certificates of ANY dimension (generalizes verification/indep/checknd.py).
# Written against the checknd spec; shares no code with gen_hd.py.  Uses only vp/order/lcm/isprime
# from verification/indep/nt.py (Agent A's first-principles helpers).
#
#   X(x) = 10^L + sum_i coefs[i]*10^{q_{i+1}} + K  must equal 2^t0 3^a 7^w   (t0 = v2(K), all coords >= qmin > t0)
#   domain (meta "domain"):
#     "ordered"   (default; = checknd):  L > q_k > ... > q_1 >= qmin, coefs[i] at q_{i+1}
#     "unordered":                       q_i pairwise distinct, qmin <= q_i < L, any order
#                                         (covers EVERY ordering of the far coefficients at once)
# Verified: (1) the tree partitions (Z/1)^dim: every lift of every internal node is a child or is
# killed by a listed rest prime; (2) every prime kill (cyclic-subgroup test, lifting to lcm(M, ord_p 10)
# when ord_p(10) does not divide M); (3) every sz leaf: signature exact and the declared solution list
# equals the set of domain points of the class with X = 2^t0 3^a0 7^w0 (exact integers);
# (4) a brute-force box: every domain solution with L <= B is recorded in an sz leaf.
# usage: python3 -I checkhd.py cert.jsonl [brute_Lmax] [workers]
import sys, os, json, math, collections, itertools
import multiprocessing as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "indep"))
from nt import vp, order, lcm, isprime

path = sys.argv[1]
BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else None
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 24
raw = [json.loads(l) for l in open(path) if l.strip()]
meta = raw[0]; assert meta['k'] == 'meta'
nodes = {n['id']: n for n in raw[1:]}
assert len(nodes) == len(raw) - 1, "duplicate ids"
DIM, COEFS, K, QMIN = meta['dim'], meta['coefs'], meta['K'], meta['qmin']
DOMAIN = meta.get('domain', 'ordered'); assert DOMAIN in ('ordered', 'unordered')
assert len(COEFS) == DIM - 1 and DIM >= 1
assert all(isinstance(c, int) and c > 0 and c % 10 != 0 for c in COEFS)
ROOT_R, ROOT_M = tuple(meta['root']['r']), meta['root']['m']
assert ROOT_M == 1 and all(x == 0 for x in ROOT_R), "root must be the whole space"
t0 = vp(K, 2)
assert K > 0 and K % 5 != 0 and QMIN > t0
if BRUTE is None: BRUTE = {1: 400, 2: 120, 3: 45, 4: 20}.get(DIM, 14)

_PR = {}
def isprime_c(p):
    if p not in _PR: _PR[p] = isprime(p)
    return _PR[p]
_TAB = {}
def tab(m, per):
    """10^e mod m for e < per (checked periodic)"""
    k = (m, per)
    if k not in _TAB:
        t = [pow(10, e, m) for e in range(per)]
        assert pow(10, per, m) == 1 % m
        _TAB[k] = t
    return _TAB[k]

def Xmod_per(r, m, per):
    if per > 50000:
        if (m, per) not in _TAB:
            assert pow(10, per, m) == 1 % m; _TAB[(m, per)] = None
        s = pow(10, r[0] % per, m) + K
        for c, e in zip(COEFS, r[1:]): s += c * pow(10, e % per, m)
        return s % m
    t = tab(m, per)
    s = t[r[0] % per] + K
    for c, e in zip(COEFS, r[1:]): s += c * t[e % per]
    return s % m

def sig(r, M):
    j = vp(M, 3); m3 = 3 ** (j + 2)
    x = Xmod_per(r, m3, 3 ** j)            # ord_{3^{j+2}}(10) = 3^j (period asserted in tab)
    a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
    if M % 6 == 0:
        i = vp(M, 7); m7 = 7 ** (i + 1)
        x = Xmod_per(r, m7, 6 * 7 ** i)
        w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
    else: w = (0, None)
    return a, w

def lifts(r, M, M2):
    f = M2 // M
    for t in itertools.product(range(f), repeat=DIM):
        yield tuple((x % M) + k * M for x, k in zip(r, t))

def kill_prime(p, r, M):
    assert isprime_c(p) and p > 7
    d = order(10, p)
    if M % d:
        M2 = lcm(M, d)
        return all(kill_prime(p, r2, M2) for r2 in lifts(r, M, M2))
    a, w = sig(r, M)
    T = Xmod_per([x % d for x in r], p, d) * pow(2, -t0, p) % p
    if T == 0: return True
    o3, o7 = order(3, p), order(7, p)
    x = T * pow(3, -a[0], p) * pow(7, -w[0], p) % p
    af, wf = a[1] is None, w[1] is None
    if af and wf: return pow(x, lcm(o3, o7), p) != 1
    if af: return pow(x, o3, p) != 1
    if wf: return pow(x, o7, p) != 1
    return x != 1

def Xval(pt):
    s = 10 ** pt[0] + K
    for c, e in zip(COEFS, pt[1:]): s += c * 10 ** e
    return s

def in_domain(pt):
    L, qs = pt[0], pt[1:]
    if L < QMIN or any(q < QMIN or q >= L for q in qs): return False
    if len(set(qs)) != len(qs): return False
    if DOMAIN == 'ordered' and any(qs[i] >= qs[i + 1] for i in range(len(qs) - 1)): return False
    return True

def domain_points_equal(N):
    """all domain points with X == N, by bounded search over L and positions (independent of the
    generator's digit decoder): 10^L <= N-K, positions in [QMIN, L)."""
    out = []
    R = N - K
    if R <= 0: return out
    Lmax = len(str(R)) - 1
    k = DIM - 1
    for L in range(QMIN, Lmax + 1):
        R1 = R - 10 ** L
        if R1 < 0: continue
        if k == 0:
            if R1 == 0: out.append((L,))
            continue
        cmax = max(COEFS)
        def rec(i, rem, used):
            if i == k:
                if rem == 0: out.append((L,) + tuple(used))
                return
            if rem <= 0: return
            # remaining coefficients can contribute at most sum c_j 10^{L-1}
            if rem > sum(COEFS[i:]) * 10 ** (L - 1): return
            for q in range(QMIN, L):
                if q in used: continue
                v = COEFS[i] * 10 ** q
                if v > rem: break
                if (rem - v) % (10 ** QMIN): continue
                rec(i + 1, rem - v, used + [q])
        rec(0, R1, [])
    return [pt for pt in out if in_domain(pt) and Xval(pt) == N]

# ---------------- pass 1: structure (serial) ----------------
problems = []
def bad(s): problems.append(s)
roots = [i for i, n in nodes.items() if n['p'] == -1]
assert len(roots) == 1
res_of = {roots[0]: (ROOT_R, ROOT_M)}
visited = set(); work = []
stack = [roots[0]]
while stack:
    i = stack.pop()
    assert i in nodes and i not in visited, ("bad/duplicate node", i); visited.add(i)
    nd = nodes[i]; r, M = res_of[i]
    assert nd['m'] == M, f"node {i}: stored modulus {nd['m']} != {M}"
    assert all(x % M == y % M for x, y in zip(nd['r'], r)), f"node {i}: stored residue mismatch"
    if nd['k'] == 'l':
        work.append(('l', i, r, M)); continue
    assert nd['k'] == 'i'
    M2 = nd['m2']; assert M2 % M == 0 and M2 > M
    ch = nd['c']
    cres = []
    for c in ch:
        assert c in nodes and nodes[c]['p'] == i, f"child {c} of {i} has wrong parent"
        cr = tuple(x % M2 for x in nodes[c]['r'])
        assert len(cr) == DIM and nodes[c]['m'] == M2
        assert all(x % M == y % M for x, y in zip(cr, r)), f"child outside parent at {i}"
        cres.append(cr); res_of[c] = (cr, M2); stack.append(c)
    assert len(set(cres)) == len(cres), f"dup children at {i}"
    work.append(('i', i, r, M))
if len(visited) != len(nodes): bad("unreachable nodes")

# ---------------- pass 2: kills (parallel) ----------------
def check_item(item):
    kind, i, r, M = item
    nd = nodes[i]; st = collections.Counter(); pr = []; claimed = []
    if kind == 'l':
        st['leaves'] += 1
        x = nd['x']
        if 'prime' in x:
            if kill_prime(x['prime'], r, M): st['leaf_prime_ok'] += 1
            else: st['leaf_prime_FAIL'] += 1; pr.append(f"leaf {i} r={r} M={M}: prime {x['prime']} fails")
        elif 'sz' in x:
            a, w = sig(r, M)
            if a[1] is None or w[1] is None: pr.append(f"leaf {i}: sz with non-exact signature {a},{w}")
            elif list(x['sz']) != [a[0], w[0]]: pr.append(f"leaf {i}: sz exponents wrong")
            else:
                N = 2 ** t0 * 3 ** a[0] * 7 ** w[0]
                sols = sorted(s for s in domain_points_equal(N) if all(si % M == ri % M for si, ri in zip(s, r)))
                if sols != sorted(tuple(s) for s in x['sol']): pr.append(f"leaf {i}: sz solutions {sols} != declared {x['sol']}")
                else: st['leaf_sz_ok'] += 1
                claimed += sols
        else: pr.append(f"leaf {i}: unknown kill {x}")
        return st, pr, claimed
    M2 = nd['m2']
    cset = {tuple(x % M2 for x in nodes[c]['r']) for c in nd['c']}
    rp = nd['rest']
    if rp is None: rp = []
    if isinstance(rp, int): rp = [rp]
    rp = list(rp)
    for rr in lifts(r, M, M2):
        if rr in cset: continue
        if not rp: pr.append(f"node {i}: lift {rr} mod {M2} neither child nor killed"); continue
        for j, p in enumerate(rp):
            if kill_prime(p, rr, M2):
                if j: rp.insert(0, rp.pop(j))       # move-to-front (order is irrelevant to the claim)
                st['rest_ok'] += 1; break
        else:
            pr.append(f"node {i}: rest lift {rr} mod {M2} survives primes {rp}"); st['rest_FAIL'] += 1
    return st, pr, claimed

def check_chunk(items):
    st = collections.Counter(); pr = []; cl = []
    for it in items:
        s, p, c = check_item(it); st.update(s); pr += p; cl += c
    return st, pr, cl

stats = collections.Counter(); claimed = set()
if WORKERS > 1 and len(work) > 200:
    nch = WORKERS * 16
    chunks = [work[i::nch] for i in range(nch)]
    with mp.get_context("fork").Pool(WORKERS) as pool:
        for st, pr, cl in pool.imap_unordered(check_chunk, chunks):
            stats.update(st); problems += pr; claimed.update(cl)
else:
    st, pr, cl = check_chunk(work); stats.update(st); problems += pr; claimed.update(cl)

# ---------------- pass 3: brute-force box ----------------
def locate(x):
    i = roots[0]
    while True:
        nd = nodes[i]
        if nd['k'] == 'l': return i
        M2 = nd['m2']; key = tuple(v % M2 for v in x); nxt = None
        for c in nd['c']:
            if tuple(v % M2 for v in nodes[c]['r']) == key: nxt = c; break
        if nxt is None: return None
        i = nxt
brute = []; npts = 0
for L in range(QMIN, BRUTE + 1):
    if DIM == 1: it = [()]
    elif DOMAIN == 'ordered': it = itertools.combinations(range(QMIN, L), DIM - 1)
    else: it = itertools.permutations(range(QMIN, L), DIM - 1)
    for qs in it:
        x = (L,) + tuple(qs); npts += 1
        X = Xval(x)
        if X % (1 << t0) or ((X >> t0) & 1) == 0: continue
        Y = X >> t0
        for pr_ in (3, 7):
            while Y % pr_ == 0: Y //= pr_
        if Y == 1:
            brute.append(x); li = locate(x)
            if li is None or 'sz' not in nodes[li]['x'] or list(x) not in [list(s) for s in nodes[li]['x']['sol']]:
                bad(f"brute solution {x} not recorded in an sz leaf")
print(f"{os.path.basename(path)}: dim={DIM} coefs={COEFS} K={K} qmin={QMIN} domain={DOMAIN} nodes={len(nodes)}")
print("   stats:", dict(stats))
print(f"   claimed solutions: {sorted(claimed)}")
print(f"   brute-force solutions in box L<={BRUTE} ({npts} pts): {brute}")
if set(brute) != {s for s in claimed if s[0] <= BRUTE}: bad("claimed vs brute mismatch")
if problems:
    print("   RESULT: FAIL"); [print("     -", p) for p in problems[:10]]; sys.exit(1)
print("   RESULT: PASS")

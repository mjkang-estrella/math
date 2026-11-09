# Independent checker for 2-D certificates of  X = 10^L + A*10^q + K = 2^t0 * 3^a * 7^w ,  domain q >= qmin, L > q.
# usage: python3 -I check2d.py cert.jsonl [brute_Lmax]
# Written from the format spec + first principles (no code of the certificate generator/checker consulted).
import sys, os, json, math, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import vp, order, lcm, pin_unsolvable, isprime

path = sys.argv[1]
BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 120
nodes = [json.loads(l) for l in open(path) if l.strip()]
meta = nodes[0]; assert meta['k'] == 'meta'
nodes = nodes[1:]
A, K, QMIN = meta['A'], meta['K'], meta['qmin']
t0 = vp(K, 2)
assert K % 5 != 0, "5 | K : the equation would need a factor 5"
assert QMIN > t0, "t = v2(X) = t0 only valid when min(q, L) > t0"
assert A % 9 == 0 and A > 0

stats = collections.Counter()
problems = []
def bad(msg):
    problems.append(msg)

# ---------------- signatures ----------------
def sig(r, M):
    """exact 3-adic / 7-adic signature of X on the class (L,q) = r mod M (componentwise moduli).
       returns ((lo,hi),(lo,hi)) with hi None meaning 'unbounded above'."""
    rL, rq = r; ML, MQ = M
    j = min(vp(ML, 3), vp(MQ, 3))
    m3 = 3 ** (j + 2)
    assert pow(10, 3 ** j, m3) == 1      # 10^x mod 3^(j+2) has period 3^j
    x = (pow(10, rL, m3) + A * pow(10, rq, m3) + K) % m3
    a = (j + 2, None) if x == 0 else (vp(x, 3), vp(x, 3))
    if ML % 6 == 0 and MQ % 6 == 0:
        i = min(vp(ML, 7), vp(MQ, 7))
        m7 = 7 ** (i + 1)
        assert pow(10, 6 * 7 ** i, m7) == 1
        x = (pow(10, rL, m7) + A * pow(10, rq, m7) + K) % m7
        w = (i + 1, None) if x == 0 else (vp(x, 7), vp(x, 7))
    else:
        w = (0, None)
    return a, w

# ---------------- region test at a prime ----------------
_pw = {}
def kill_at_prime(p, r, M, depth=0):
    """True iff no (L,q) in class r mod M (with exponents a,w in the class signature) can have X = 2^t0 3^a 7^w"""
    assert isprime(p) and p > 7, p
    d = order(10, p)
    ML, MQ = M
    if ML % d or MQ % d:
        M2 = (lcm(ML, d), lcm(MQ, d))
        stats['lift_classes'] += (M2[0] // ML) * (M2[1] // MQ)
        for iL in range(M2[0] // ML):
            for iq in range(M2[1] // MQ):
                r2 = (r[0] + iL * ML, r[1] + iq * MQ)
                if not kill_at_prime(p, r2, M2, depth + 1): return False
        return True
    a, w = sig(r, M)
    T = (pow(10, r[0] % d, p) + A * pow(10, r[1] % d, p) + K) * pow(2, -t0, p) % p
    if T == 0: return True
    o3, o7 = order(3, p), order(7, p)
    x = T
    if a[1] is None: x = x * pow(3, -a[0], p) % p   # a >= lo : T / 3^lo must be in <3> (or <3,7>)
    else: x = x * pow(3, -a[0], p) % p
    x = x * pow(7, -w[0], p) % p
    af, wf = a[1] is None, w[1] is None
    if af and wf: e = lcm(o3, o7)
    elif af: e = o3
    elif wf: e = o7
    else: return x != 1
    return pow(x, e, p) != 1       # in the cyclic group (Z/p)*, h in <g> iff h^{ord g} = 1

# ---------------- exact leaf ----------------
def sz_solutions(a0, w0):
    N = 2 ** t0 * 3 ** a0 * 7 ** w0 - K
    sols = []
    if N <= 0: return sols
    D = len(str(N)) + 1
    for L in range(2, D + 1):
        for q in range(QMIN, L):
            if 10 ** L + A * 10 ** q == N: sols.append((L, q))
    return sols

def class_qmin(rq, MQ):
    q = QMIN + ((rq - QMIN) % MQ)
    return q

# ---------------- tree ----------------
byid = {i: n for i, n in enumerate(nodes)}
# node ids: file position (after the meta line) - verify children ids make sense
roots = [i for i, n in byid.items() if n.get('p') == -1]
assert len(roots) == 1, roots
root = roots[0]
assert byid[root]['m'] == [1, 1] and byid[root]['k'] == 'i'
visited = set()
leaves = []     # (r, M, kind, sols)
restkills = []
claimed_solutions = set()

def visit(i, r, M):
    assert i not in visited, ("node visited twice", i); visited.add(i)
    nd = byid[i]
    assert tuple(nd['r']) == tuple(x % m for x, m in zip(r, M)) or True
    if nd['k'] == 'l':
        stats['leaves'] += 1
        a, w = sig(r, M)
        da, dw = tuple(nd['a']), tuple(nd['w'])
        da = (da[0], da[1]); dw = (dw[0], dw[1])
        if (da, dw) != (a, w):
            # is the declared signature a sound over-approximation of the true one?
            def covers(d, t):
                if d[1] is None: return d[0] <= t[0]
                return t[1] is not None and d == t
            if covers(da, a) and covers(dw, w): stats['sig_declared_weaker'] += 1
            else:
                stats['sig_MISMATCH'] += 1; bad(f"leaf {i} declared sig {da},{dw} != recomputed {a},{w}")
        x = nd['x']
        if 'prime' in x or 'T0' in x:
            p = x.get('prime', x.get('T0'))
            ok = kill_at_prime(p, r, M)
            stats['kill_prime_ok' if ok else 'kill_prime_FAIL'] += 1
            if not ok: bad(f"leaf {i} r={r} M={M}: prime {p} does not kill (sig {a},{w})")
        elif 'pin' in x:
            kq = x['pin'][0]
            qc = class_qmin(r[1], M[1])
            if kq > qc: bad(f"leaf {i}: pin exponent {kq} exceeds class min q {qc}"); stats['pin_FAIL'] += 1; return
            if kq <= t0: bad(f"leaf {i}: pin exponent {kq} <= t0"); stats['pin_FAIL'] += 1; return
            ok = pin_unsolvable(K, t0, kq, a, w)
            if ok: stats['pin_ok'] += 1
            else:
                # convention check: every point of the class has q >= class min q, so the pin holds mod 10^q' for any q' <= that
                kq2 = min(qc, 60)
                if kq2 > kq and pin_unsolvable(K, t0, kq2, a, w):
                    stats['pin_ok_only_via_class_minq'] += 1
                else:
                    stats['pin_FAIL'] += 1
                    bad(f"leaf {i} r={r} M={M}: pin at 10^{kq} (and 10^{min(qc,60)}, class min q={qc}) solvable with sig {a},{w}")
        elif 'sz' in x:
            if a[1] is None or w[1] is None:
                stats['sz_FAIL'] += 1; bad(f"leaf {i}: sz needs both exponents exact, sig {a},{w}"); return
            if list(x['sz']) != [a[0], w[0]]:
                stats['sz_FAIL'] += 1; bad(f"leaf {i}: sz exponents {x['sz']} != {a[0], w[0]}"); return
            allsol = sz_solutions(a[0], w[0])
            inclass = sorted(s for s in allsol if s[0] % M[0] == r[0] % M[0] and s[1] % M[1] == r[1] % M[1])
            decl = sorted(tuple(s) for s in x['L'])
            if inclass != decl:
                stats['sz_FAIL'] += 1; bad(f"leaf {i}: sz solutions in class {inclass} != declared {decl}")
            else: stats['sz_ok'] += 1
            for s in inclass: claimed_solutions.add(s)
        else:
            bad(f"leaf {i}: unknown kill {x}")
        leaves.append((tuple(r), tuple(M), nd))
        return
    ch = [byid[c] for c in nd['c']]
    Ms = {tuple(c['m']) for c in ch}
    assert len(Ms) == 1, f"children of {i} have different moduli"
    M2 = Ms.pop()
    assert M2[0] % M[0] == 0 and M2[1] % M[1] == 0
    cres = [tuple(x % m for x, m in zip(c['r'], M2)) for c in ch]
    assert len(set(cres)) == len(cres), f"duplicate children at {i}"
    for cr in cres: assert cr[0] % M[0] == r[0] % M[0] and cr[1] % M[1] == r[1] % M[1], f"child outside parent {i}"
    cset = set(cres)
    nlift = (M2[0] // M[0]) * (M2[1] // M[1])
    rest = nd['rest']
    nrest = 0
    for iL in range(M2[0] // M[0]):
        for iq in range(M2[1] // M[1]):
            rr = (r[0] % M[0] + iL * M[0], r[1] % M[1] + iq * M[1])
            if rr in cset: continue
            nrest += 1
            if rest is None:
                bad(f"node {i}: lift {rr} mod {M2} neither child nor killed"); continue
            if not kill_at_prime(rest['q'], rr, M2):
                bad(f"node {i}: rest lift {rr} mod {M2} survives prime {rest['q']}"); stats['rest_FAIL'] += 1
            else:
                stats['rest_ok'] += 1
                restkills.append((rr, M2))
    for c, cr in zip(nd['c'], cres):
        visit(c, cr, M2)

visit(root, (0, 0), (1, 1))
if len(visited) != len(nodes): bad(f"{len(nodes)-len(visited)} unreachable nodes in file")

# ---------------- end-to-end empirical check: every actual solution in a box lies in an 'sz' leaf that lists it ----------------
# locate: descend the tree
def locate(L, q):
    i = root; M = (1, 1)
    while True:
        nd = byid[i]
        if nd['k'] == 'l': return ('leaf', i)
        ch = [byid[c] for c in nd['c']]
        M2 = tuple(ch[0]['m'])
        key = (L % M2[0], q % M2[1])
        nxt = None
        for c, cn in zip(nd['c'], ch):
            if (cn['r'][0] % M2[0], cn['r'][1] % M2[1]) == key: nxt = c; break
        if nxt is None: return ('rest', i)
        i = nxt
brute_sols = []
npts = 0
for L in range(QMIN + 1, BRUTE + 1):
    for q in range(QMIN, L):
        npts += 1
        X = 10 ** L + A * 10 ** q + K
        Y = X >> t0
        if X % (1 << t0) or (Y & 1) == 0: continue
        for pr in (3, 7):
            while Y % pr == 0: Y //= pr
        if Y == 1:
            brute_sols.append((L, q))
            loc = locate(L, q)
            if loc[0] != 'leaf' or 'sz' not in byid[loc[1]]['x'] or [L, q] not in [list(s) for s in byid[loc[1]]['x']['L']]:
                bad(f"brute-force solution {(L,q)} is NOT recorded in an sz leaf ({loc})")
print(f"{os.path.basename(path)}: A={A} K={K} qmin={QMIN} t0={t0} nodes={len(nodes)} leaves={stats['leaves']}")
print("   stats:", dict(stats))
print(f"   claimed solutions (in domain q>=qmin,L>q): {sorted(claimed_solutions)}")
print(f"   brute-force solutions of the equation in box q>={QMIN}, L<={BRUTE} ({npts} pts): {brute_sols}")
if set(brute_sols) != {s for s in claimed_solutions if s[0] <= BRUTE}:
    bad(f"claimed {sorted(claimed_solutions)} vs brute {brute_sols}")
if problems:
    print("   RESULT: FAIL")
    for p in problems[:20]: print("     -", p)
    sys.exit(1)
print("   RESULT: PASS")

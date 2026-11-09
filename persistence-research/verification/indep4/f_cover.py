# F: independent coverage map for the 121 nd-sym closures of target 14112.  stdlib only; python3 -I f_cover.py
import sys, json, itertools, collections, glob, os
sys.dont_write_bytecode = True
T = 14112
DIGS = (2, 3, 4, 6, 7, 8, 9)
SYM = '../highdim/sym/'

def v2(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

# ---- 1. my own enumeration of all configurations (S_low, sorted far A-values)
def multisets(t):
    out = []
    def rec(rem, mn, cur):
        if rem == 1: out.append(tuple(cur)); return
        for d in DIGS:
            if d >= mn and rem % d == 0:
                cur.append(d); rec(rem // d, d, cur); cur.pop()
    rec(t, 2, [])
    return out

def configs(t):
    res = {}
    for ms in multisets(t):
        cm = collections.Counter(ms)
        for pat in itertools.product((1,) + DIGS, repeat=3):
            used = collections.Counter(d for d in pat if d != 1)
            if any(used[d] > cm[d] for d in used): continue
            far = sorted((cm - used).elements())
            S = sum((d - 1) * 10 ** i for i, d in enumerate(pat))
            key = (S, tuple(9 * (c - 1) for c in far))
            assert key not in res
            res[key] = (ms, pat)
    return res

C = configs(T)

# ---- 1b. model check: every digit string with product T and <= 10 digits is in exactly one config, and 9n = 10^L + K + sum A 10^q
def digit_strings(maxlen):
    out = []
    def rec(rem, digs):
        if rem == 1 and len(digs) >= 3: out.append(tuple(digs))
        if len(digs) == maxlen: return
        for d in (1,) + DIGS:
            if d == 1 or rem % d == 0:
                digs.append(d); rec(rem // d if d != 1 else rem, digs); digs.pop()
    rec(T, [])
    return out
nstr = 0
for ds in digit_strings(9):          # ds[i] = digit at position i (least significant first)
    L = len(ds)
    if ds[-1] != 1 and False: pass
    n = sum(d * 10 ** i for i, d in enumerate(ds))
    S = sum((d - 1) * 10 ** i for i, d in enumerate(ds[:3]))
    far = sorted(d for d in ds[3:] if d != 1)
    key = (S, tuple(9 * (c - 1) for c in far))
    assert key in C, key
    K = 9 * S - 1
    assert 9 * n == 10 ** L + K + sum(9 * (d - 1) * 10 ** i for i, d in enumerate(ds) if i >= 3)
    nstr += 1
print("model check: %d digit strings (len<=9, product %d) all map to a config and satisfy 9n = 10^L + K + sum A 10^q" % (nstr, T))

# ---- optional comparison with E's enumerator
sys.path.insert(0, '../indep2')
import e_enum
CE = e_enum.configs(T)
assert set(CE) == set(C), "enumeration differs from E"
print("my config set == E's config set: %d configs" % len(C))

# ---- 2. slices (my recursion).  state: (K', multiset R of A's still free, p = next position to decide)
def slices(K, R):
    """list of (K', sorted R, qmin) partitioning all placements of the far digits R at distinct positions >= 3."""
    out = []
    def rec(K, R, p):
        t0 = v2(K)
        if p >= t0 + 1 and p >= 3:        # positions < p already decided; everything free is >= p > t0
            out.append((K, tuple(sorted(R)), p)); return
        # decide position p: digit 1 there, or one of the distinct free A's
        rec(K, R, p + 1)
        for v in sorted(set(R)):
            R2 = list(R); R2.remove(v)
            rec(K + v * 10 ** p, R2, p + 1)
    rec(K, list(R), 3)
    return out

# ---- 3. load certificates
closed = json.load(open(SYM + 'summary.json'))['closed']
assert len(closed) == len(set(closed)) == 121
audit = json.load(open(SYM + 'coverage_audit.json'))['configurations']
metas = {}
for f in sorted(glob.glob(SYM + 'certs/*/*.jsonl')):
    metas[f] = json.loads(open(f).readline())

# my checker results
res = {}
for f in glob.glob('logs/all/*.json'):
    r = json.load(open(f))
    res[os.path.abspath(r['file'])] = r

def parse(key):
    s, far = key.split('|')
    return int(s), tuple(sorted(int(x) for x in far.split(',')))

report = []; nbad = 0
used_certs = collections.Counter()
for key in closed:
    S, far = parse(key)
    row = dict(key=key, status='?')
    if (S, far) not in C: row['status'] = 'NOT A CONFIG'; nbad += 1; report.append(row); continue
    K = 9 * S - 1
    sl = slices(K, far)
    row['K'] = K; row['t0'] = v2(K); row['slices'] = [(a, list(b), c) for a, b, c in sl]
    covered = []
    for (Kp, R, qm) in sl:
        grp = sorted(collections.Counter(R).items())
        hits = []
        for f, m in metas.items():
            if m['K'] != Kp or sorted(map(tuple, m['groups'])) != grp: continue
            if not (m['qmin'] <= qm and m['scope'] == 'full' and m['domain'] == 'unordered' and m['root']['m'] == 1): continue
            if m['qmin'] <= v2(Kp): continue
            r = res.get(os.path.abspath(f))
            if r and r['result'] == 'PASS' and not r['claimed']: hits.append(f)
        covered.append((Kp, R, qm, hits))
        for h in hits: used_certs[h] += 1
    ok = all(h for *_, h in covered)
    # compare with M's declared mapping (only as a cross-reference)
    mine = sorted(h for *_, hs in covered for h in hs)
    theirs = sorted(SYM + d for d in audit['new:14112:' + key]['domains'])
    row['status'] = 'COVERED' if ok else 'UNCOVERED'
    row['certs'] = [os.path.relpath(h, SYM) for h in mine]
    row['matches_M_mapping'] = (mine == theirs)
    if not ok: nbad += 1
    report.append(row)
print("configs:", len(report), " covered:", sum(r['status'] == 'COVERED' for r in report), " not covered:", nbad)
print("all K odd (t0=0):", all(r['t0'] == 0 for r in report), "; every config has exactly one slice (qmin=3):", all(len(r['slices']) == 1 and r['slices'][0][2] == 3 for r in report))
print("mapping equals M's coverage_audit mapping for", sum(r['matches_M_mapping'] for r in report), "of", len(report))
print("distinct certificates used:", len(used_certs), " max configs per cert:", max(used_certs.values()))
unused = [os.path.relpath(f, SYM) for f in metas if f not in used_certs]
print("certificate files not used by the 121 closures:", len(unused))
json.dump(dict(report=report, unused=unused), open('f_cover_out.json', 'w'), indent=1)

# ---- 4. finite part: smooth-lattice scan.  Every n with digit product T and L<=D digits; which configs do the members fall in?
D = 60
mem = []
lim = 10 ** D
for i in range(0, 200):
    a = 2 ** i
    if a >= lim: break
    for j in range(0, 130):
        b = a * 3 ** j
        if b >= lim: break
        for k in range(0, 80):
            n = b * 7 ** k
            if n >= lim: break
            s = str(n); p = 1
            for ch in s:
                p *= int(ch)
                if p == 0 or p > T: break
            if p == T: mem.append(n)
print("members (digit product %d) among 7-smooth n < 10^%d: %s" % (T, D, sorted(mem)))
for n in mem:
    ds = [int(c) for c in str(n)][::-1]
    S = sum((d - 1) * 10 ** i for i, d in enumerate(ds[:3])); far = sorted(d for d in ds[3:] if d != 1)
    key = (S, tuple(9 * (c - 1) for c in far))
    print("  member", n, "config", "%d|%s" % (key[0], ','.join(map(str, key[1]))), "in closed list:", ("%d|%s" % (key[0], ','.join(map(str, key[1])))) in set(closed))

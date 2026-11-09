# F: independent coverage map for a sample of sym2 closed configurations (target 14112).  python3 -I sym2/f_cover2.py cfg_sample.json resultsdir
import sys, json, os, collections, itertools
sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)
T = 14112; DIGS = (2, 3, 4, 6, 7, 8, 9)
SYM2 = '../highdim/sym2/'
sample = json.load(open(sys.argv[1])); resdir = sys.argv[2]
SCANL = 200                   # smooth lattice scanned to 10^200 (f_scan.py): only member 33718272

def v2(n):
    k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k

def multisets(t):
    out = []
    def rec(rem, mn, cur):
        if rem == 1: out.append(tuple(cur)); return
        for d in DIGS:
            if d >= mn and rem % d == 0:
                cur.append(d); rec(rem // d, d, cur); cur.pop()
    rec(t, 2, []); return out
def configs(t):
    res = {}
    for ms in multisets(t):
        cm = collections.Counter(ms)
        for pat in itertools.product((1,) + DIGS, repeat=3):
            used = collections.Counter(d for d in pat if d != 1)
            if any(used[d] > cm[d] for d in used): continue
            far = sorted((cm - used).elements())
            S = sum((d - 1) * 10 ** i for i, d in enumerate(pat))
            res[(S, tuple(9 * (c - 1) for c in far))] = (ms, pat)
    return res
C = configs(T)
summ = json.load(open(SYM2 + 'summary.json'))['configurations']

def load_result(f):
    name = f.split('/certs/')[-1].replace('/', '__') + '.json'
    p = os.path.join(resdir, name)
    if not os.path.exists(p): return None
    return json.load(open(p))

report = []
tot_certs = 0; tot_pass = 0
for ck in json.load(open(sys.argv[1])):
    cfg = summ[ck]; key = cfg['key']
    S, far = int(key.split('|')[0]), tuple(sorted(int(x) for x in key.split('|')[1].split(',')))
    row = dict(config=ck, method=cfg['coverage_method'], dim=cfg['dim'], listed_domains=cfg['domain_count'])
    if (S, far) not in C: row['status'] = 'NOT A CONFIG'; report.append(row); continue
    K0 = 9 * S - 1
    idx = collections.defaultdict(list)       # (K', R) -> [(qmin, file, result)]
    problems = []; nmiss = 0
    for f in cfg['domains']:
        m = json.loads(open(f).readline())
        rr = load_result(f); tot_certs += 1
        if rr is None: nmiss += 1; continue
        ok = (rr['result'] == 'PASS' and m['scope'] == 'full' and m['domain'] == 'unordered' and m['root']['m'] == 1
              and m['qmin'] > v2(m['K']))
        tot_pass += ok
        if not ok: continue
        R = tuple(sorted(a for a, mu in m['groups'] for _ in range(mu)))
        idx[(m['K'], R)].append((m['qmin'], f, rr))
    pmax = max([q for l in idx.values() for q, _, _ in l] + [3]) + 1
    used = {}; uncovered = []; states = [0]
    memo = {}
    def cover(K, R, p):
        k = (K, R, p)
        if k in memo: return memo[k]
        states[0] += 1
        best = None
        for q, f, rr in idx.get((K, R), ()):
            if R:
                if q <= p: best = (q, f, rr); break
            else:
                if q <= SCANL + 1: best = (q, f, rr); break      # L < q handled by the exact smooth scan (L<=200)
        if best is not None:
            used[(K, R, best[0])] = best[1]; memo[k] = True; return True
        if p > pmax:
            uncovered.append((K, R, p)); memo[k] = False; return False
        ok = cover(K, R, p + 1)                       # no far digit at position p
        for v in sorted(set(R)):                      # or one far digit of value v
            R2 = list(R); R2.remove(v)
            ok = cover(K + v * 10 ** p, tuple(R2), p + 1) and ok
        memo[k] = ok; return ok
    ok = cover(K0, far, 3)
    claimed = []
    for (K, R, q), f in used.items():
        rr = load_result(f)
        for s in rr.get('claimed', []): claimed.append((f, s))
    row.update(status='COVERED' if ok else 'UNCOVERED', slices_used=len(used), states=states[0], uncovered=uncovered[:3], not_run=nmiss,
               used_not_listed=0, t0_K0=v2(K0), claimed_in_used=len(claimed),
               max_t0_used=max([v2(K) for (K, R, q) in used] + [0]), max_qmin_used=max([q for (K, R, q) in used] + [0]))
    row['claimed'] = [(f.split('/certs/')[-1], s) for f, s in claimed][:5]
    report.append(row)
    print(ck, row['status'], 'slices', len(used), 'states', states[0], 'unrun', nmiss, 'claimed', len(claimed), flush=True)
json.dump(report, open(os.path.join(resdir, 'cover_report.json'), 'w'), indent=1)
print('configs', len(report), 'covered', sum(r['status'] == 'COVERED' for r in report), 'certs examined', tot_certs, 'PASS', tot_pass)

"""Read-only frozen-artifact replay and preregistered independent checks."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import gcd, isqrt
from pathlib import Path
import json
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEST = HERE / 'H012-review-audit.json'
if DEST.exists():
    raise SystemExit('Refusing to overwrite review evidence')
START = time.monotonic()
DEADLINE = START + 55
OUT = {'scope': 'Independent replay; no new factoring/scaling experiment',
       'stages': [], 'failures': [], 'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
       'preregistration_sha256': sha256((HERE/'H012-review-preregister.md').read_bytes()).hexdigest()}


def tick():
    if time.monotonic() >= DEADLINE:
        raise TimeoutError('55-second review deadline')


def root(n, k):
    x = 1 << ((n.bit_length()+k-1)//k)
    while True:
        y = ((k-1)*x + n//x**(k-1))//k
        if y >= x:
            assert x**k <= n < (x+1)**k
            return x
        x = y


def round_up_tie(a, b):
    q, r = divmod(a, b)
    return q + (2*r >= b)


def qrange(a, b, c, lo, hi):
    points = [Fraction(lo), Fraction(hi)]
    if a:
        v = Fraction(-b, 2*a)
        if lo <= v <= hi:
            points.append(v)
    vals = [a*x*x+b*x+c for x in points]
    return min(vals), max(vals)


def rational_oracle(cert, n, lo, hi, H):
    u, v, t = cert
    return (qrange(u, v-H, n*t, lo, hi)[1] <= 0 and
            qrange(u, v+H, n*t, lo, hi)[0] >= 0)


def independent_runs(indices):
    ends = []
    for i in sorted(indices):
        if not ends or i > ends[-1][1]+1:
            ends.append([i, i])
        else:
            ends[-1][1] = i
    return ends


def optimum(k, pool):
    # Shortest path on the first uncovered cell, independent of greedy.
    runs = [r for p in pool for r in independent_runs(p['covered_cells'])]
    dp = [k+1]*(k+1)
    dp[0] = 0
    for i in range(k):
        for l, r in runs:
            if l <= i <= r:
                dp[r+1] = min(dp[r+1], dp[i]+1)
    return None if dp[k] > k else dp[k]


def reduced_basis(n, m, c, C):
    a, b = (m*C*C, 0), (c*C*C, n)
    steps, peak = 0, 0
    def dot(x, y):
        return x[0]*y[0]+x[1]*y[1]
    while True:
        tick()
        steps += 1
        peak = max(peak, dot(a, a).bit_length(), dot(b, b).bit_length())
        if dot(a, a) > dot(b, b):
            a, b = b, a
        q = round_up_tie(dot(a, b), dot(a, a))
        if not q:
            assert abs(a[0]*b[1]-a[1]*b[0]) == m*C*C*n
            assert 2*abs(dot(a, b)) <= dot(a, a) <= dot(b, b)
            return a, b, steps, peak
        b = (b[0]-q*a[0], b[1]-q*a[1])


def frozen_replay():
    paths = ['research/experiments/H012/certificate_reuse.py',
             'research/hypotheses/H012.md', 'research/experiments/H012/result.json']
    wanted = ['181e97caeef68b373b639fdb3f510b0811a7c902eb83e2f6ca1ea13cb04f0f13',
              '17f456aa1727cff5657d7de00e66251bce3d4b27e2de2d09b5574956c00bc456',
              '77b7d6573586a7eda648473c1cb850ee35bbb3f9fff6a269ecc70e59378f9a07']
    hashes = {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}
    assert list(hashes.values()) == wanted
    data = json.loads((ROOT/paths[2]).read_text())
    assert data['source_sha256'] == wanted[0] and data['protocol_sha256'] == wanted[1]
    # Load only definitions, without main, filesystem writes, or bytecode caches.
    namespace = {'__name__': 'frozen_readonly_review'}
    exec(compile((ROOT/paths[0]).read_text(), paths[0], 'exec'), namespace)
    global FROZEN
    FROZEN = namespace
    totals = Counter()
    rows = []
    widths = Counter()
    for ri, row in enumerate(data['rows']):
        tick()
        assert row['status'] == 'complete' and row['error'] is None
        n, m, j, K, H = (row[x] for x in ('N','m','j','K','H'))
        assert gcd(n,m) == gcd(j,m) == 1 and 0 < j < m
        target = root(n, 5)
        assert m <= target < 2*m
        corpus = next(c for c in data['corpus'] if c['N'] == n)
        rest = m
        for p in corpus['m_prime_factors']:
            assert p >= 2 and all(p % d for d in range(2,isqrt(p)+1))
            assert rest % p == 0
            while rest % p == 0:
                rest //= p
        assert rest == 1
        kroot = isqrt(n//m**3)
        kroot += kroot*kroot*m**3 < n
        assert K == 16*kroot and H == K*m*m
        lo = root(n,3)
        lo += lo**3 < n
        hi = isqrt(n)
        cells = []
        while lo < hi:
            end = min(2*lo,hi)
            cells.append([lo,end])
            lo = end
        assert cells == row['cells']
        generated = {}
        gauss, peak = 0, 0
        c = n*pow(j*j,-1,m) % m
        invj = pow(j,-1,m*m)
        for ci,(lo,hi) in enumerate(cells):
            C = (lo+hi)//2
            a,b,gs,pb = reduced_basis(n,m,c,C)
            gauss += gs
            peak = max(peak,pb)
            vecs = [a,b,(a[0]+b[0],a[1]+b[1]),(a[0]-b[0],a[1]-b[1])]
            for x,y in vecs:
                assert x % (C*C) == 0 and y % n == 0
                u,t = x//(C*C),y//n
                if u < 0 or (u == 0 and t < 0):
                    u,t = -u,-t
                vr = (-u*j-n*t*invj) % (m*m)
                v = vr + m*m*round_up_tie(-u*C*C-n*t-vr*C,m*m*C)
                generated.setdefault((u,v,t),[]).append(ci)
        assert [(list(c),s) for c,s in generated.items()] == [
            (p['certificate'],p['source_cells']) for p in row['pool']]
        counts = row['counts']
        assert counts['gauss_steps'] == gauss
        assert counts['selected_peak_bits'] == peak
        assert counts['generated_vectors'] == 4*len(cells)
        assert counts['envelope_checks'] == len(cells)*len(row['pool'])
        for item in row['pool']:
            u,v,t = item['certificate']
            assert u or t
            assert (v+2*u*j) % m == 0
            assert (n*t+u*j*j+v*j) % (m*m) == 0
            for ci in item['source_cells']:
                C = sum(cells[ci])//2
                residual = u*C*C+v*C+n*t
                assert -m*m*C < 2*residual <= m*m*C
            covered = []
            for ci,(lo,hi) in enumerate(cells):
                tick()
                ok = rational_oracle((u,v,t),n,lo,hi,H)
                assert ok == FROZEN['envelope']((u,v,t),n,lo,hi,H)
                assert ok == FROZEN['independent_envelope']((u,v,t),n,lo,hi,H)
                if ok:
                    covered.append(ci)
                vals = [u*hi*hi,v*hi,n*t,H*hi,4*u*n*t,(v-H)**2,(v+H)**2]
                widths[str(n.bit_length())] = max(widths[str(n.bit_length())],
                                                 *(abs(x).bit_length() for x in vals))
            assert covered == item['covered_cells']
            totals['certificates'] += 1
        opt = optimum(len(cells), row['pool'])
        assert opt == row['selected_interval_count'] == len(row['selected'])
        assert row['complete_cover'] and row['first_gap'] is None
        covered_selected = set()
        for s in row['selected']:
            l,r = s['cells']
            assert [l,r] in independent_runs(row['pool'][s['pool_index']]['covered_cells'])
            covered_selected.update(range(l,r+1))
        assert covered_selected == set(range(len(cells)))
        assert row['selected_distinct_certificates'] == len({s['pool_index'] for s in row['selected']})
        assert row['compression_ratio'] == len(cells)/opt
        totals.update({k:v for k,v in counts.items() if k != 'selected_peak_bits'})
        rows.append({'row':ri,'bits':n.bit_length(),'status':'pass','certificates':len(row['pool']),
                     'cell_count':len(cells),'minimum_interval_count':opt,
                     'axis_certificates':sum(p['certificate'][0]*p['certificate'][2] == 0 for p in row['pool']),
                     'maximum_run_cells':max((r-l+1 for p in row['pool'] for l,r in independent_runs(p['covered_cells'])),default=0)})
    assert len(rows) == 96
    return {'hashes':hashes,'rows':rows,'totals':dict(totals),
            'independently_observed_envelope_expression_peak_bits':dict(widths),
            'note':'Widths are selected expression diagnostics, not a complete bit-operation meter.'}


def edge_envelopes():
    count = 0
    for n,u,t,v,H,(lo,hi) in product([1,2,3,7],range(-3,4),range(-3,4),
                                    range(-5,6),[0,1,2,5],[(1,1),(1,2),(2,5),(3,7)]):
        tick()
        cert = (u,v,t)
        expected = rational_oracle(cert,n,lo,hi,H)
        assert FROZEN['envelope'](cert,n,lo,hi,H) == expected,(cert,n,lo,hi,H)
        assert FROZEN['independent_envelope'](cert,n,lo,hi,H) == expected,(cert,n,lo,hi,H)
        count += 1
    return {'cases':count,'mismatches':0}


def greedy_edges():
    count = complete = 0
    for k in range(1,5):
        for size in range(4):
            for masks in combinations(range(1 << k),size):
                tick()
                pool = [{'covered_cells':[i for i in range(k) if (mask >> i)&1]} for mask in masks]
                expected = optimum(k,pool)
                ok,selected,gap = FROZEN['cover'](k,pool)
                assert ok == (expected is not None)
                if ok:
                    assert len(selected) == expected and gap is None
                    complete += 1
                count += 1
    return {'cases':count,'complete':complete,'incomplete':count-complete,'mismatches':0}


def rectangle_identity():
    outcomes = []
    def phi(n):
        return sum(gcd(a,n) == 1 for a in range(1,n+1))
    for m,(U,T) in product([6,30,210,2310],[(2,3),(7,11),(17,23)]):
        tick()
        units = [c for c in range(m) if gcd(c,m) == 1]
        per_c = []
        for c in units:
            tick()
            count = sum((u-c*t)%m == 0 for u in range(-U,U+1) if u
                        for t in range(-T,T+1) if t)
            per_c.append(count)
        expected = Fraction(0)
        for d in range(1,m+1):
            if m % d:
                continue
            q = m//d
            A = sum(gcd(a,q) == 1 for a in range(-U//d-1,U//d+1) if a and abs(a)*d <= U)
            B = sum(gcd(b,q) == 1 for b in range(-T//d-1,T//d+1) if b and abs(b)*d <= T)
            expected += Fraction(A*B,phi(q))
        actual = Fraction(sum(per_c),len(units))
        assert actual == expected,(m,U,T,actual,expected)
        outcomes.append({'m':m,'U':U,'T':T,'unit_count':len(units),
                         'total_pairs_over_units':sum(per_c),'exact_mean':str(actual),
                         'units_with_nonzero_pair':sum(x > 0 for x in per_c),'status':'pass'})
    return {'cases':outcomes,'mismatches':0}


STAGES = [('frozen_replay',frozen_replay),('edge_envelopes',edge_envelopes),
          ('greedy_edges',greedy_edges),('rectangle_identity',rectangle_identity)]
for name,fn in STAGES:
    t0 = time.monotonic()
    try:
        tick()
        result = fn()
        OUT['stages'].append({'name':name,'status':'pass','seconds':time.monotonic()-t0,'result':result})
    except Exception as exc:
        OUT['stages'].append({'name':name,'status':'failed','seconds':time.monotonic()-t0})
        OUT['failures'].append({'stage':name,'error':repr(exc),'traceback':traceback.format_exc()})
        break
for name,_ in STAGES[len(OUT['stages']):]:
    OUT['stages'].append({'name':name,'status':'unstarted'})
OUT['seconds'] = time.monotonic()-START
OUT['status'] = 'pass' if not OUT['failures'] and all(s['status']=='pass' for s in OUT['stages']) else 'failed'
DEST.write_text(json.dumps(OUT,indent=2)+'\n')
print(json.dumps({'status':OUT['status'],'seconds':OUT['seconds'],
                  'stages':[{k:v for k,v in s.items() if k!='result'} for s in OUT['stages']],
                  'failures':OUT['failures']}))

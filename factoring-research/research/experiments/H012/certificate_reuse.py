"""Exact primitive screen; no factoring or asymptotic claim from cover ratios."""
import hashlib
import json
import math
import random
import statistics
import time
from collections import Counter
from pathlib import Path

CONFIG = {'bits': [64, 128, 256], 'samples': 2, 'residues': 16,
          'seed': 1212, 'seconds': 55, 'K_multiplier': 16}


def root_floor(n, k):
    lo, hi = 0, 1 << ((n.bit_length()+k-1)//k)
    while hi-lo > 1:
        mid = (hi+lo)//2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi**k <= n else lo


def prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))


def modulus(n):
    target = root_floor(n, 5)
    m, p, factors = 1, 2, []
    while m*p <= target:
        m *= p
        factors.append(p)
        p += 1
        while not prime(p):
            p += 1
    while 2*m <= target:
        m *= 2
    return m, factors


def nearest(num, den):
    assert den > 0
    return (2*num+den)//(2*den)


def reduce_basis(b1, b2, counts, deadline):
    while True:
        if time.monotonic() >= deadline:
            raise TimeoutError
        counts['gauss_steps'] += 1
        norm1, norm2 = sum(x*x for x in b1), sum(x*x for x in b2)
        counts['selected_peak_bits'] = max(counts['selected_peak_bits'], norm1.bit_length(), norm2.bit_length())
        if norm2 < norm1:
            b1, b2 = b2, b1
            norm1 = norm2
        dot = sum(x*y for x, y in zip(b1, b2))
        q = nearest(dot, norm1)
        if q == 0:
            return b1, b2
        b2 = tuple(y-q*x for x, y in zip(b1, b2))


def envelope(cert, n, lo, hi, H):
    u, v, t = cert
    w = n*t
    for z in (lo, hi):
        if abs(u*z*z+v*z+w) > H*z:
            return False
    inside = (u*lo*lo <= w <= u*hi*hi) if u > 0 else (u*hi*hi <= w <= u*lo*lo)
    if u*t <= 0 or not inside:
        return True
    four = 4*u*w
    if u > 0:
        upper = H-v >= 0 and four <= (H-v)**2
        lower = -H-v <= 0 or four >= (-H-v)**2
    else:
        upper = v-H <= 0 or four >= (v-H)**2
        lower = v+H >= 0 and four <= (v+H)**2
    return upper and lower


def independent_envelope(cert, n, lo, hi, H):
    # Multiply by positive z and test the extrema of two quadratics instead.
    u, v, t = cert
    w = n*t
    for z in (lo, hi):
        if u*z*z+(v-H)*z+w > 0 or u*z*z+(v+H)*z+w < 0:
            return False
    if u < 0:
        b, den = v-H, -2*u
        if den*lo <= b <= den*hi and 4*u*w-b*b < 0:
            return False
    if u > 0:
        b, den = v+H, 2*u
        if den*lo <= -b <= den*hi and 4*u*w-b*b < 0:
            return False
    return True


def cells_for(n):
    start = root_floor(n, 3)
    if start**3 < n:
        start += 1
    end = math.isqrt(n)
    cells = []
    while start < end:
        nxt = min(2*start, end)
        cells.append((start, nxt))
        start = nxt
    return cells


def ranges(indices):
    out = []
    for i in indices:
        if out and out[-1][1]+1 == i:
            out[-1][1] = i
        else:
            out.append([i, i])
    return out


def cover(cell_count, pool):
    available = [(lo, hi, i) for i, item in enumerate(pool)
                 for lo, hi in ranges(item['covered_cells'])]
    selected, cursor = [], 0
    while cursor < cell_count:
        choices = [x for x in available if x[0] <= cursor <= x[1]]
        if not choices:
            return False, selected, cursor
        best = max(choices, key=lambda x: (x[1], -x[2], -x[0]))
        selected.append({'pool_index': best[2], 'cells': [best[0], best[1]]})
        cursor = best[1]+1
    return True, selected, None


def run_case(n, m, j, cells, K, deadline):
    counts, lookup = Counter(), {}
    H, m2 = K*m*m, m*m
    start = time.monotonic()
    generation_seconds = None
    status, error = 'complete', None
    pool = []
    try:
        c = n*pow(j*j, -1, m) % m
        jinv = pow(j, -1, m2)
        for index, (lo, hi) in enumerate(cells):
            C = (lo+hi)//2
            b1, b2 = reduce_basis((m*C*C, 0), (c*C*C, n), counts, deadline)
            vectors = [b1, b2, tuple(x+y for x, y in zip(b1,b2)),
                       tuple(x-y for x, y in zip(b1,b2))]
            for b in vectors:
                counts['generated_vectors'] += 1
                assert b[0] % (C*C) == 0 and b[1] % n == 0
                u, t = b[0]//(C*C), b[1]//n
                assert u or t
                if u < 0 or (u == 0 and t < 0):
                    u, t = -u, -t
                residue = (-u*j-n*t*jinv) % m2
                target = -u*C*C-n*t
                v = residue+nearest(target-residue*C, m2*C)*m2
                cert = (u,v,t)
                assert (v+2*u*j) % m == 0
                assert (n*t+u*j*j+v*j) % m2 == 0
                if cert not in lookup:
                    lookup[cert] = {'certificate': list(cert), 'source_cells': [], 'covered_cells': []}
                lookup[cert]['source_cells'].append(index)
        generation_seconds = time.monotonic()-start
        pool = list(lookup.values())
        for item in pool:
            for index, (lo, hi) in enumerate(cells):
                if time.monotonic() >= deadline:
                    raise TimeoutError
                counts['envelope_checks'] += 1
                actual = envelope(item['certificate'], n, lo, hi, H)
                expected = independent_envelope(item['certificate'], n, lo, hi, H)
                assert actual == expected, ('envelope', item['certificate'], lo, hi, H)
                if actual:
                    item['covered_cells'].append(index)
        complete_cover, selected, first_gap = cover(len(cells), pool)
    except TimeoutError:
        status, error = 'partial', 'deadline'
    except AssertionError as exc:
        status, error = 'error', repr(exc)
    if status != 'complete':
        pool = list(lookup.values())
        complete_cover, selected, first_gap = None, [], None
    return {'N':n, 'bits':n.bit_length(), 'm':m, 'j':j, 'K':K, 'H':H,
            'status':status, 'error':error, 'cells':cells, 'pool':pool,
            'complete_cover':complete_cover, 'selected':selected, 'first_gap':first_gap,
            'selected_interval_count':len(selected),
            'selected_distinct_certificates':len({x['pool_index'] for x in selected}),
            'compression_ratio':len(cells)/len(selected) if complete_cover else None,
            'counts':dict(counts), 'generation_seconds':generation_seconds,
            'seconds':time.monotonic()-start}


def main():
    here = Path(__file__).resolve().parent
    dest = here/'result.json'
    if dest.exists():
        raise SystemExit('Refusing to overwrite evidence.')
    start = time.monotonic()
    deadline = start+CONFIG['seconds']
    rng = random.Random(CONFIG['seed'])
    corpus, generation = [], []
    for bits in CONFIG['bits']:
        selected, rejected = [], 0
        while len(selected) < CONFIG['samples'] and time.monotonic() < deadline:
            n = rng.getrandbits(bits) | (1 << (bits-1)) | 1
            m, factors = modulus(n)
            if math.gcd(n,m) != 1 or n in selected:
                rejected += 1
                continue
            selected.append(n)
            corpus.append({'N':n,'m':m,'m_prime_factors':factors})
        generation.append({'bits':bits,'selected':selected,'rejections':rejected,
                           'sample_shortfall':CONFIG['samples']-len(selected)})
    for item in corpus:
        residues, rejections = [], 0
        while len(residues) < CONFIG['residues'] and time.monotonic() < deadline:
            j = rng.randrange(1,item['m'])
            if math.gcd(j,item['m']) != 1 or j in residues:
                rejections += 1
            else:
                residues.append(j)
        item.update({'residues':residues,'residue_rejections':rejections,
                     'residue_shortfall':CONFIG['residues']-len(residues)})
    rows = []
    for item in corpus:
        n,m = item['N'],item['m']
        kroot = math.isqrt(n//(m**3))
        if kroot*kroot*m**3 < n:
            kroot += 1
        K,cells = CONFIG['K_multiplier']*kroot,cells_for(n)
        for j in item['residues']:
            rows.append(run_case(n,m,j,cells,K,deadline) if time.monotonic() < deadline
                        else {'N':n,'bits':n.bit_length(),'m':m,'j':j,'status':'unstarted'})
    summaries = []
    for bits in CONFIG['bits']:
        group = [r for r in rows if r['bits']==bits]
        done = [r for r in group if r['status']=='complete']
        ratios = [r['compression_ratio'] for r in done if r['complete_cover']]
        summaries.append({'bits':bits,'status_counts':dict(Counter(r['status'] for r in group)),
                          'fully_complete':len(done)==CONFIG['samples']*CONFIG['residues'],
                          'incomplete_covers':sum(not r['complete_cover'] for r in done),
                          'median_compression':statistics.median(ratios) if ratios else None,
                          'median_selected':statistics.median(r['selected_interval_count'] for r in done) if done else None,
                          'cell_counts':sorted({len(r['cells']) for r in done})})
    largest = next((s for s in reversed(summaries) if s['fully_complete']),None)
    disposition = ('soundness_failure' if any(r['status']=='error' for r in rows)
                   else 'inconclusive' if largest is None else
                   'finite_continuation_threshold_passed' if not largest['incomplete_covers'] and largest['median_compression']>=2
                   else 'finite_pool_rejected')
    output = {'schema':1,'config':CONFIG,'generation':generation,'corpus':corpus,'rows':rows,
              'summaries':summaries,'disposition':disposition,'seconds':time.monotonic()-start,
              'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'protocol_sha256':hashlib.sha256((here.parents[1]/'hypotheses/H012.md').read_bytes()).hexdigest(),
              'scope':'Exact certificate primitive screen; no semiprime promise, matched factoring benchmark, or asymptotic gain.'}
    dest.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'summaries':summaries,'disposition':disposition,'seconds':output['seconds']}))


if __name__=='__main__':
    main()

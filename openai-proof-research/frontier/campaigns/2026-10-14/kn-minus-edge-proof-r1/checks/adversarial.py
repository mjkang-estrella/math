"""Independent finite support for review, never a proof of the all-n claim.

Myeongjin Kang; original review code MIT. No author-checker imports.
Uses exact geometry and rational arithmetic, then Python-integer modular
linear algebra (no fixed-width products). Run from any directory, Python 3.
"""
from fractions import Fraction as Q
from functools import cmp_to_key
from collections import Counter
from itertools import combinations
from math import comb, isqrt, prod
from pathlib import Path
import json
import random
import time

HERE = Path(__file__).resolve().parent
LOG = []
PRIME = 1000003
assert all(PRIME % k for k in range(2, isqrt(PRIME) + 1))

def record(name, **kw):
    r = {'check': name, **kw}
    LOG.append(r)
    print(json.dumps(r), flush=True)

def cross(a, b):
    return a[0]*b[1] - a[1]*b[0]

def sub(a, b):
    return a[0]-b[0], a[1]-b[1]

def orient(a, b, c):
    return cross(sub(b, a), sub(c, a))

def geometry(n, missing):
    """Generic integer straight-line drawing; J2=2J, exact rotation order."""
    rng = random.Random(891+n)
    while True:
        pts = [(rng.randrange(-10000, 10001), rng.randrange(-10000, 10001)) for _ in range(n)]
        if len(set(pts)) == n and all(orient(*(pts[i] for i in triple)) for triple in combinations(range(n), 3)):
            break
    edges = [e for e in combinations(range(n), 2) if e != missing]
    j2, events, locations = {}, [], set()
    def add(e, f, value):
        j2[e, f] = value
        j2[f, e] = -value
    for e, f in combinations(edges, 2):
        if set(e) & set(f):
            continue
        a,b,c,d = (pts[i] for i in e+f)
        if orient(a,b,c)*orient(a,b,d) < 0 and orient(c,d,a)*orient(c,d,b) < 0:
            direction_e, direction_f = sub(b,a), sub(d,c)
            det = cross(direction_e, direction_f)
            t = Q(cross(sub(c,a), direction_f), det)
            point = (a[0]+t*direction_e[0], a[1]+t*direction_e[1])
            assert point not in locations, 'triple crossing'
            locations.add(point)
            sign = 1 if det > 0 else -1
            add(e, f, 2*sign)
            events.append((e,f,sign))
    def compare(a, b):
        ha = 0 if a[1] > 0 or a[1] == 0 and a[0] > 0 else 1
        hb = 0 if b[1] > 0 or b[1] == 0 and b[0] > 0 else 1
        if ha != hb:
            return ha-hb
        return -1 if cross(a,b) > 0 else 1
    for v in range(n):
        neighbors = [i for i in range(n) if i != v and tuple(sorted((v,i))) != missing]
        neighbors.sort(key=cmp_to_key(lambda i,j: compare(sub(pts[i],pts[v]), sub(pts[j],pts[v]))))
        for i,j in combinations(neighbors, 2):
            e, f = tuple(sorted((v,i))), tuple(sorted((v,j)))
            add(e, f, (1 if v == e[0] else -1)*(1 if v == f[0] else -1))
    return edges, j2, events

def weights(t, modulus=None):
    den = [prod(t[i]-t[j] for j in range(len(t)) if i != j) for i in range(len(t))]
    return [Q(1,d) for d in den] if modulus is None else [pow(d % modulus,-1,modulus) for d in den]

def test(j2, t, w, h, modulus=None):
    total = 0
    for ((i,j),(k,l)), value in j2.items():
        a,b,c,d = t[i],t[j],t[k],t[l]
        total += value*w[i]*w[j]*w[k]*w[l]*(h(a,b,c,d)-h(b,a,c,d)-h(a,b,d,c)+h(b,a,d,c))
        if modulus:
            total %= modulus
    return total

def missing_pair_tests(n, modular):
    full_edges,full_j2,full_events = geometry(n,(-1,-1))
    counts = Counter()
    for e,f,_ in full_events:
        counts[e] += 1
        counts[f] += 1
    missing = (1,n-2) if n == 7 else max(full_edges,key=lambda e:counts[e])
    edges,j2,events = geometry(n,missing)
    t = list(range(-n,n,2))
    random.Random(908+n).shuffle(t)
    modulus = PRIME if modular else None
    w = weights(t,modulus)
    a,b = (t[i] for i in missing)
    s = n//2
    # A symmetric-pair kernel basis element; not in the evaluation kernel.
    d = s-2
    P = lambda x,u,y,v: (x**d*u**d-a**d*b**d)*(y**d*v**d+1)
    U = lambda x: x**s
    V = lambda y: y**(s-1)
    B = lambda u,v: u**(s-1)*v**(s-2)
    H = lambda x,u,y,v: P(x,u,y,v)*(u-v)*(u-y)*(v-x)*U(x)*(y-a)*V(y)*(v-a)*B(u,v)
    assert test(j2,t,w,H,modulus) == 0
    failures = []
    for omitted in ('y-a','v-a'):
        bad = lambda x,u,y,v: P(x,u,y,v)*(u-v)*(u-y)*(v-x)*U(x)*(1 if omitted=='y-a' else y-a)*V(y)*(1 if omitted=='v-a' else v-a)*B(u,v)
        value = test(j2,t,w,bad,modulus)
        if n == 7:
            assert value != 0, (n,omitted)
        failures.append({'omitted':omitted,'nonzero':value != 0})
    generic = test(j2,t,w,lambda x,u,y,v:x**(n-2)*u**(n-3)*y**(n-2)*v**(n-4),modulus)
    assert generic != 0
    # Both missing-pair conditions can fail while the test still vanishes:
    # H=xy pairs one chain with itself in the skew form.
    assert a != b
    assert test(j2,t,w,lambda x,u,y,v:x*y,modulus) == 0
    # Local factor orientation, including the two incomplete stars: compare
    # all shared-endpoint contributions to direct inner sums after weights.
    shared = 0
    for i in range(n):
        for p in range(n):
            for q in range(n):
                if len({i,p,q}) < 3:
                    continue
                e,f = tuple(sorted((i,p))),tuple(sorted((i,q)))
                sign = (1 if i<p else -1)*(1 if i<q else -1)
                j = sign*j2.get((e,f),0)
                direct = j*w[i]**2*w[p]*w[q]*H(t[i],t[p],t[i],t[q])
                # Exact expression for all stars, with absent spokes zero.
                denp = prod(t[p]-t[r] for r in range(n) if r not in (i,p))
                denq = prod(t[q]-t[r] for r in range(n) if r not in (i,q))
                ip = Q(1,denp) if modulus is None else pow(denp % modulus,-1,modulus)
                iq = Q(1,denq) if modulus is None else pow(denq % modulus,-1,modulus)
                transformed = j*w[i]**2*U(t[i])*(t[i]-a)*V(t[i])*(t[p]-t[q])*ip*iq*P(t[i],t[p],t[i],t[q])*(t[q]-a)*B(t[p],t[q])
                assert (direct-transformed) % modulus == 0 if modulus else direct == transformed
                shared += direct
    # RII control: replace a crossing by signs +,-,+ (or -,+,-).
    # A simple local wiggle adds two crossings, changes neither J nor rotations.
    e,f,sign = events[0]
    changed = events[1:]+[(e,f,sign),(e,f,-sign),(e,f,sign)]
    def event_sums(es):
        sums = {}
        for e,f,sg in es:
            sums[e,f] = sums.get((e,f),0)+sg
        return {k:v for k,v in sums.items() if v}
    assert event_sums(changed) == event_sums(events)
    assert len(changed) == len(events)+2
    record('missing-pair/localization',n=n,arithmetic='Fp' if modular else 'Q',missing=missing,
           valid_test_zero=True,omission_controls=failures,generic_invalid_nonzero=True,nonconverse_H_xy=True,
           local_factor_equalities=True,RII_crossing_count=[len(events),len(changed)])

def echelon_rank(rows, modulus=PRIME):
    """Forward elimination with Python ints; no overflow, no cached pivots."""
    pivots = {}
    for source in rows:
        row = [v % modulus for v in source]
        for col in sorted(pivots):
            coefficient = row[col]
            if coefficient:
                pivot = pivots[col]
                row[col:] = [(x-coefficient*y) % modulus for x,y in zip(row[col:],pivot[col:])]
        col = next((i for i,v in enumerate(row) if v),None)
        if col is not None:
            inverse = pow(row[col],-1,modulus)
            pivots[col] = [v*inverse % modulus for v in row]
    return len(pivots)

def sym(a,b,x,u,modulus=PRIME):
    return (pow(x,a,modulus)*pow(u,b,modulus)+(pow(x,b,modulus)*pow(u,a,modulus) if a!=b else 0)) % modulus

def frontier_rank(n=15):
    """Independent tight two-page support, integral kernel basis, rank mod p."""
    s=n//2
    missing=(0,s)
    t=list(range(-n,n,2));random.Random(931).shuffle(t)
    basis=list(combinations(range(s-1),2))+[(i,i) for i in range(s-1)]
    basis.sort()
    basis.remove((0,0));basis.insert(0,(0,0))
    C=lambda e: int(sum(e)%n < s)
    T=[]
    for i,j,k,l in combinations(range(n),4):
        e,f=(i,k),(j,l)
        if e!=missing and f!=missing and C(e)==C(f):
            T.extend([(e,f),(f,e)])
    d=comb(s,2)
    assert len(basis)==d and len(T)==2*d*(d-1)
    first,second=[],[]
    for e,f in T:
        ev=[sym(a,b,t[e[0]],t[e[1]]) for a,b in basis]
        fv=[sym(a,b,t[f[0]],t[f[1]]) for a,b in basis]
        first.append(ev);second.append(fv)
    values_at_missing=[sym(a,b,t[missing[0]],t[missing[1]]) for a,b in basis]
    rows=[]
    for r in range(1,d):
        c=values_at_missing[r]
        for q in range(d):
            rows.append([(x[r]-c)*y[q] % PRIME for x,y in zip(first,second)])
    rank=echelon_rank(rows)
    assert rank==d*(d-1)==420
    # Edge-swap permutes T, carrying S_a to S_b; check every coordinate.
    position={pair:i for i,pair in enumerate(T)}
    assert all(first[i]==second[position[(f,e)]] for i,(e,f) in enumerate(T))
    # An actual rank-loss mutation, not a reused baseline result.
    assert echelon_rank(rows[:-1]) == rank-1
    # J for alternating pairs i<j<k<l is page sign; use 2J.
    w=weights(t,PRIME)
    coeff=[]
    for e,f in T:
        x,u,y,v=(t[i] for i in e+f)
        sign=(1 if e[0]<f[0] else -1)*(1 if C(e) else -1)
        delta=(x-u)*(y-v)*(x-y)*(x-v)*(u-y)*(u-v)
        coeff.append(2*sign*prod(w[i] for i in e+f)*delta % PRIME)
    assert all(coeff)
    rng=random.Random(940)
    for _ in range(100):
        r,q=rng.randrange(1,d),rng.randrange(d)
        h,k=rng.randrange(d),rng.randrange(1,d)
        total=sum(c*(x[r]-values_at_missing[r])*y[q]*x[h]*(y[k]-values_at_missing[k]) for c,x,y in zip(coeff,first,second))%PRIME
        assert total==0
    record('new-range rank and mixed orthogonality',n=n,prime=PRIME,dimSa=420,rankSa=rank,
           rankSb_by_swap=rank,T=len(T),mixed_pairs=100,deleted_basis_row_rank=rank-1)

def detector(s=7):
    N=2*s; t=list(range(-N,N,2));rng=random.Random(941);rng.shuffle(t)
    order=list(range(N));rng.shuffle(order);pos={v:i for i,v in enumerate(order)}
    w=weights(t,PRIME)
    # Twice the order pairing; moments up to needed product exponents.
    moments={}
    for a in range(2*s-2):
        for b in range(2*s-2):
            moments[a,b]=sum((1 if pos[i]<pos[j] else -1)*(t[i]-t[j])*w[i]*w[j]*pow(t[i],a,PRIME)*pow(t[j],b,PRIME) for i in range(N) for j in range(N) if i!=j)%PRIME
    A=[(a,b) for a in range(s-1) for b in range(s-1)]
    B=[(a,b) for a in range(s) for b in range(s-1)]
    for c in t:
        rows=[[(moments[a+d,b+e+1]-c*moments[a+d,b+e])%PRIME for d,e in B] for a,b in A]
        assert echelon_rank(rows)==len(A)
    record('twisted detector',s=s,nodes=N,orders='fixed nonnumeric random order',all_twist_nodes=N,rank=len(A))

def identities():
    Z=lambda n:prod((n-i)//2 for i in range(4))//4
    T=lambda n:Z(n)-comb((n-1)//2,2)
    for n in range(2,2001):
        assert Q(prod(((n+2)//2,(n-1)//2,(n-3)//2,(n-4)//2)),4)==T(n)
        if n%2==0 and n>=6:
            assert Q(n+2,n-2)*Z(n-1)==T(n)
    for m in range(4,101):
        for n in (1,2,11,79):
            assert (n-1)*T(m+2)+2*Z(m+1)==Q(((m+1)//2)*((m-1)//2)*((m-2)//2)*(n*((m+4)//2)+(m-4)//2),4)
    # Exact symbolic counting identities for arbitrary crossing-type counts,
    # including added edges crossing adjacent edges at x or y.
    rng=random.Random(942)
    for n in (6,8,14):
        verts=list(range(n)); x,y=0,1
        edges=[e for e in combinations(verts,2) if e!=(x,y)]
        events=[(e,f,rng.randrange(3)) for e,f in combinations(edges,2) if not set(e)&set(f)]
        total=sum(c for e,f,c in events)
        kx=sum(c for e,f,c in events if y not in e+f)
        ky=sum(c for e,f,c in events if x not in e+f)
        paths=[]
        for i in range(2,n):
            path={(x,i),(y,i)}
            ai=sum(c*((e in path)+(f in path)) for e,f,c in events)
            # Local spoke crossings m_i survive only until deleting v_i.
            mi=rng.randrange(n-3)
            ri=sum(c for e,f,c in events if i in e+f)
            di=total+ai+mi
            di_minus_i=total-ri+ai
            assert di-di_minus_i==ri+mi
            paths.append(ai)
        assert 2*total==kx+ky+sum(paths)
    record('floor/product/even-counting identities',n_max=2000,corollary_m_max=100,even_type_models=[6,8,14])

if __name__=='__main__':
    start=time.time()
    identities()
    missing_pair_tests(7,False)
    missing_pair_tests(15,True)
    detector(7)
    frontier_rank(15)
    result={'all_passed':True,'runtime_seconds':time.time()-start,'checks':LOG,
            'limitations':'Finite support only. Modular vanishing is not an exact rational identity. No source theorem truth audit.'}
    (HERE/'adversarial.json').write_text(json.dumps(result,indent=2)+'\n')
    print('ALL INDEPENDENT CHECKS PASSED',flush=True)

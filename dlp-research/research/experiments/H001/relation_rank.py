#!/usr/bin/env python3
"""Bounded algebra diagnostic; neither a DLP solver nor an n=5 cost experiment.

Counts explicit modular arithmetic, predicates, selected matrix/point accesses,
loop iterations and random draws. Does not count Python/runtime instructions,
allocation bytes or hardware work. Global instrumented-event cap is 1,000,000.
"""
import collections
import hashlib
import json
import random
import time
import sys
from pathlib import Path

LIMIT = 1_000_000
COUNTS = collections.Counter()

def event(name, n=1):
    if sum(COUNTS.values()) + n > LIMIT:
        raise RuntimeError('instrumented event budget exhausted')
    COUNTS[name] += n

def add(a, b, p):
    event('mod_add')
    return (a+b) % p

def sub(a, b, p):
    event('mod_sub')
    return (a-b) % p

def mul(a, b, p):
    event('mod_mul')
    return (a*b) % p

def power(a, e, p):
    r = 1
    while e:
        event('loop')
        if e & 1:
            r = mul(r, a, p)
        a = mul(a, a, p)
        e >>= 1
    return r

def eq(a, b):
    event('predicate')
    return a == b

def prime(n):
    event('predicate')
    if n < 2:
        return False
    d = 2
    while d*d <= n:
        event('loop')
        event('integer_divisibility')
        if n % d == 0:
            return False
        d += 1
    return True

def draw(rng, n):
    event('random_draw')
    return rng.randrange(n)

def make_curve(p):
    # p = 3 mod 4, nonspecial a,b nonzero, prime full curve order;
    # reject anomalous q=p and embedding degree <=4. All trials are charged.
    rng = random.Random(20261008+p)
    for attempts in range(1, 101):
        event('loop')
        a = draw(rng, p-1)+1
        b = draw(rng, p-1)+1
        disc = add(mul(4, mul(mul(a,a,p),a,p),p),
                   mul(27,mul(b,b,p),p),p)
        if eq(disc, 0):
            continue
        points = []
        q = 1
        for x in range(p):
            event('loop')
            rhs = add(add(mul(mul(x,x,p),x,p),mul(a,x,p),p),b,p)
            if eq(rhs, 0):
                event('point_write')
                points.append((x,0))
                q += 1
            elif eq(power(rhs,(p-1)//2,p), 1):
                y = power(rhs,(p+1)//4,p)
                assert eq(mul(y,y,p), rhs)
                event('point_write')
                points.append((x,min(y,p-y)))
                q += 2
        if not prime(q) or eq(q,p):
            continue
        small_embedding = False
        for k in range(1,5):
            event('loop')
            if eq(power(p,k,q),1):
                small_embedding = True
                break
        if small_embedding:
            continue
        return {'p':p,'a':a,'b':b,'q':q,'curve_trials':attempts}, points
    raise RuntimeError('curve generation exhausted 100 trials')

def f3(x, y, z, a, b, p):
    # Standard expanded third Semaev polynomial. Direct evaluation, no oracle.
    xy = mul(x,y,p)
    xm = sub(x,y,p)
    term1 = mul(mul(xm,xm,p),mul(z,z,p),p)
    inner = add(mul(add(x,y,p),add(xy,a,p),p),mul(2,b,p),p)
    term2 = mul(mul(2,inner,p),z,p)
    xya = sub(xy,a,p)
    term3 = mul(xya,xya,p)
    term4 = mul(mul(4,b,p),add(x,y,p),p)
    return sub(add(sub(term1,term2,p),term3,p),term4,p)

def coefficients(z, a, b, p):
    # C with f3(x,y,z) = (1,x,x^2) C (1,y,y^2)^T.
    z2 = mul(z,z,p)
    c00 = sub(mul(a,a,p),mul(mul(4,b,p),z,p),p)
    c01 = sub(sub(0,mul(mul(2,a,p),z,p),p),mul(4,b,p),p)
    c11 = sub(sub(0,mul(2,z2,p),p),mul(2,a,p),p)
    c12 = sub(0,mul(2,z,p),p)
    return [[c00,c01,z2],[c01,c11,c12],[z2,c12,1]]

def bilinear(x,y,C,p):
    vx = [1,x,mul(x,x,p)]
    vy = [1,y,mul(y,y,p)]
    ans = 0
    for i in range(3):
        for j in range(3):
            event('loop')
            event('matrix_read')
            ans = add(ans,mul(mul(vx[i],C[i][j],p),vy[j],p),p)
    return ans

def rank(matrix,p):
    # Exact Gaussian elimination; inverses are actual counted modular powering.
    n = len(matrix)
    event('matrix_read',n*n)
    event('matrix_write',n*n)
    A = [row[:] for row in matrix]
    r = 0
    pivots = []
    for c in range(n):
        event('loop')
        pivot = None
        for i in range(r,n):
            event('loop')
            event('matrix_read')
            if not eq(A[i][c],0):
                pivot = i
                break
        if pivot is None:
            continue
        event('matrix_read',2*n)
        event('matrix_write',2*n)
        A[r],A[pivot] = A[pivot],A[r]
        event('matrix_read')
        inv = power(A[r][c],p-2,p)
        for j in range(c,n):
            event('loop')
            event('matrix_read')
            A[r][j] = mul(A[r][j],inv,p)
            event('matrix_write')
        for i in range(r+1,n):
            event('loop')
            event('matrix_read')
            factor = A[i][c]
            if eq(factor,0):
                continue
            for j in range(c,n):
                event('loop')
                event('matrix_read',2)
                A[i][j] = sub(A[i][j],mul(factor,A[r][j],p),p)
                event('matrix_write')
        pivots.append((r,c))
        r += 1
        if r == n:
            break
    return r,pivots

def point_add(P,Q,a,p):
    # Used solely to verify each zero entry has an actual signed point relation.
    event('point_add_attempt')
    if P is None:
        return Q
    if Q is None:
        return P
    x,y = P
    u,v = Q
    if eq(x,u):
        if eq(add(y,v,p),0):
            return None
        numerator = add(mul(3,mul(x,x,p),p),a,p)
        denominator = mul(2,y,p)
    else:
        numerator = sub(v,y,p)
        denominator = sub(u,x,p)
    assert not eq(denominator,0)
    slope = mul(numerator,power(denominator,p-2,p),p)
    xx = sub(sub(mul(slope,slope,p),x,p),u,p)
    yy = sub(mul(slope,sub(x,xx,p),p),y,p)
    return xx,yy

def signed_zero(P,Q,R,a,p):
    for s in (1,-1):
        for t in (1,-1):
            event('loop')
            Ps = (P[0],P[1] if s==1 else sub(0,P[1],p))
            Qt = (Q[0],Q[1] if t==1 else sub(0,Q[1],p))
            S = point_add(Ps,Qt,a,p)
            event('predicate')
            if S is not None and eq(S[0],R[0]) and (
                    eq(S[1],R[1]) or eq(S[1],sub(0,R[1],p))):
                return True
    return False

def snapshot():
    return dict(COUNTS)

def difference(before):
    return {k:COUNTS[k]-before.get(k,0) for k in sorted(COUNTS)
            if COUNTS[k]-before.get(k,0)}

def main():
    started = time.monotonic()
    out = {'scope':'rank of f3 values versus rank of zero-incidence, not n=5',
           'limit':LIMIT,'event_convention':__doc__,'curves':[],'datasets':[],
           'verified_dlp_improvement':'NONE'}
    try:
        for p,B in ((59,20),(127,24),(251,32)):
            before = snapshot()
            curve,points = make_curve(p)
            curve['preprocessing_events'] = difference(before)
            out['curves'].append(curve)
            a,b,q = curve['a'],curve['b'],curve['q']
            assert B <= len(points)
            for seed in (7,19,43):
                before = snapshot()
                rng = random.Random(seed)
                # Draw without replacement; retries and random draws count.
                chosen = []
                indices = set()
                while len(chosen) < B:
                    event('loop')
                    i = draw(rng,len(points))
                    event('predicate')
                    if i not in indices:
                        indices.add(i)
                        event('point_read')
                        chosen.append(points[i])
                        event('point_write')
                event('point_read')
                R = points[draw(rng,len(points))]
                C = coefficients(R[0],a,b,p)
                M,Z = [],[]
                edges = []
                decomposition_checks = 0
                for i,P in enumerate(chosen):
                    mr,zr = [],[]
                    for j,Q in enumerate(chosen):
                        event('loop')
                        v = f3(P[0],Q[0],R[0],a,b,p)
                        # Full factorization identity checked once per row.
                        if j == 0:
                            assert eq(v,bilinear(P[0],Q[0],C,p))
                            decomposition_checks += 1
                        zero = eq(v,0)
                        mr.append(v)
                        zr.append(int(zero))
                        event('matrix_write',2)
                        if zero:
                            assert signed_zero(P,Q,R,a,p)
                            edges.append((i,j))
                    M.append(mr)
                    Z.append(zr)
                value_rank,value_pivots = rank(M,p)
                zero_rank,zero_pivots = rank(Z,p)
                assert value_rank <= 3
                row = {'p':p,'a':a,'b':b,'q':q,'B':B,'seed':seed,
                       'target':R,'factor_base':chosen,
                       'value_rank':value_rank,'zero_incidence_rank':zero_rank,
                       'zero_edges':edges,'all_zero_edges_group_verified':True,
                       'bilinear_checks':decomposition_checks,
                       'value_pivots':value_pivots,'zero_pivots':zero_pivots,
                       'matrix_cell_peak':3*B*B,
                       'events':difference(before)}
                out['datasets'].append(row)
        out['completed'] = True
    except Exception as exc:
        out['completed'] = False
        out['failure'] = type(exc).__name__+': '+str(exc)
    out['total_events'] = snapshot()
    out['total_event_count'] = sum(COUNTS.values())
    out['elapsed_seconds'] = time.monotonic()-started
    out['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out['low_rank_zero_inference_falsified'] = any(
        r['value_rank'] <= 3 and r['zero_incidence_rank'] > 3
        for r in out['datasets'])
    dest = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_suffix('.json')
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('completed','total_event_count',
        'elapsed_seconds','low_rank_zero_inference_falsified',
        'verified_dlp_improvement')}))
    for row in out['datasets']:
        print(json.dumps({k:row[k] for k in ('p','q','B','seed','value_rank',
            'zero_incidence_rank','all_zero_edges_group_verified')}))
    if not out['completed']:
        print(out.get('failure','unknown failure'))
        raise SystemExit(1)

if __name__ == '__main__':
    main()

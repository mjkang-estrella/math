# MathDB 348799 (Balister-Gyori-Schelp conjecture): for nonzero v_1..v_{2^(n-1)} in F_2^n summing to 0,
# F_2^n splits into pairs {p_i,q_i} with p_i+q_i=v_i. Solver: cover smallest uncovered point x by x+v for an
# unused value v (branch over distinct remaining values). Modes: exhaustive n (all multisets), random n trials.
import sys,itertools,random,json,time
from collections import Counter
class Budget(Exception): pass
def solvable(n,mult,limit=None,rng=None):
    # returns True/False, or None if node budget exceeded. Branch on the uncovered point with fewest options.
    N=1<<n; cnt=Counter(mult); covered=[False]*N; nodes=[0]
    def rec(rem):
        if rem==0: return True
        nodes[0]+=1
        if limit and nodes[0]>limit: raise Budget
        vals=[v for v in cnt if cnt[v]>0]
        best=None;bopt=None
        for x in range(N):
            if covered[x]: continue
            opts=[v for v in vals if not covered[x^v]]
            if best is None or len(opts)<len(bopt):
                best=x;bopt=opts
                if len(opts)<=1: break
        if not bopt: return False
        x=best; covered[x]=True
        if rng: rng.shuffle(bopt)
        for v in bopt:
            cnt[v]-=1; covered[x^v]=True
            if rec(rem-1): return True
            cnt[v]+=1; covered[x^v]=False
        covered[x]=False
        return False
    try: return rec(N//2)
    except Budget: return None
mode=sys.argv[1]; n=int(sys.argv[2]); t0=time.time()
if mode=='exh':
    tested=0; bad=[]
    for ms in itertools.combinations_with_replacement(range(1,1<<n),1<<(n-1)):
        s=0
        for v in ms: s^=v
        if s: continue
        tested+=1
        if not solvable(n,ms): bad.append(ms)
    print(json.dumps(dict(mode=mode,n=n,zero_sum_multisets=tested,unsolvable=len(bad),bad=bad[:5],sec=round(time.time()-t0,1))))
else:
    T=int(sys.argv[3]); rng=random.Random(2026); bad=[]; hard=[]; tested=0; kinds=Counter()
    m=1<<(n-1)
    while tested<T and time.time()-t0<100:
        kind=rng.choice(['uniform','fewvalues','subspace','skewed'])
        if kind=='uniform': ms=[rng.randrange(1,1<<n) for _ in range(m-1)]
        elif kind=='fewvalues':
            vals=[rng.randrange(1,1<<n) for _ in range(rng.randint(2,5))]; ms=[rng.choice(vals) for _ in range(m-1)]
        elif kind=='subspace':
            d=rng.randint(2,n-1); basis=[rng.randrange(1,1<<n) for _ in range(d)]
            def rv():
                while True:
                    x=0
                    for b in basis:
                        if rng.random()<0.5: x^=b
                    if x: return x
            ms=[rv() for _ in range(m-1)]
        else:
            a=rng.randrange(1,1<<n); ms=[a if rng.random()<0.7 else rng.randrange(1,1<<n) for _ in range(m-1)]
        s=0
        for v in ms: s^=v
        if s==0: continue
        ms.append(s); tested+=1; kinds[kind]+=1
        r=solvable(n,ms,limit=20000)
        rr=0
        while r is None and rr<40:
            rr+=1; r=solvable(n,ms,limit=5000,rng=rng)
        if r is None: hard.append(sorted(ms))
        elif not r: bad.append(sorted(ms))
    print(json.dumps(dict(mode=mode,n=n,tested=tested,kinds=kinds,unsolvable=len(bad),bad=bad[:3],budget_exceeded=len(hard),hard=hard[:3],sec=round(time.time()-t0,1))))

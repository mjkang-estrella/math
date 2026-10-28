"""Exact temporal-column constraint graph, for a period-p rule115 orbit.

A triple (left,mid,right) is legal iff all p time-update equations hold.
Finiteness of the initial two rows implies uniform temporal background outside
some interval, by finite propagation for the first p time steps. Thus a finite
p-periodic configuration gives a finite spatial walk from (bg,bg) to itself.
This is an exploratory checker, not a formal certificate.
"""
import json
import sys
from collections import deque

def graph(p):
    mask=(1<<p)-1
    def rot(x): return ((x<<1)&mask)|(x>>(p-1))
    def invrot(x): return (x>>1)|((x&1)<<(p-1))
    valid=[x for x in range(1<<p) if (((rot(x)^invrot(x))|x)==mask)]
    dy={x:rot(x)^invrot(x) for x in valid}
    bg=sum(1<<t for t in range(p) if t%3==1)
    root=(bg,bg)
    edges={}; reverse={}
    def legal(l,m,r): return dy[m]==(((~m)|(l&~r))&mask)
    # Reachability suffices; do not materialize unreachable pairs.
    q=deque([root]); seen={root}
    while q:
        l,m=q.popleft()
        out=[]
        for r in valid:
            if legal(l,m,r):
                v=(m,r);out.append(v)
                reverse.setdefault(v,[]).append((l,m))
                if v not in seen:seen.add(v);q.append(v)
        edges[l,m]=out
    q=deque([root]);back={root}
    while q:
        for v in reverse.get(q.popleft(),[]):
            if v not in back:back.add(v);q.append(v)
    core=seen&back
    def three(x):return rot(rot(rot(x)))==x
    bad=[v for v in core if not all(three(x) for x in v)]
    return dict(p=p,valid_columns=len(valid),reachable_pairs=len(seen),
        returnable_pairs=len(core),non_three_periodic_pairs=len(bad),
        core=[[format(x,f'0{p}b') for x in v] for v in sorted(core)],
        bad_sample=bad[:5])

if __name__=='__main__':
    for p in map(int,sys.argv[1:] or ['3','6','9','12']):
        print(json.dumps(graph(p)),flush=True)

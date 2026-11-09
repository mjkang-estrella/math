# 373112: find spanning Laman graphs B on n vertices with no tight set X, 4<=|X|<=n-1 ("free" bases of R_n),
# and with no single exchange B-e+f isomorphic to B.
import sys,json,time,pathlib,itertools
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from g6 import parse
def ecount(adj,X):
    c=0; m=X
    while m:
        v=(m&-m).bit_length()-1; m&=m-1; c+=bin(adj[v]&X).count('1')
    return c//2
def laman_free(n,adj):
    E=ecount(adj,(1<<n)-1)
    if E!=2*n-3: return False,False
    free=True
    for X in range(1,1<<n):
        k=bin(X).count('1')
        if k<2: continue
        c=ecount(adj,X)
        if c>2*k-3: return False,False
        if c==2*k-3 and 4<=k<=n-1: free=False
    return True,free
def canon(n,edges):
    best=None
    for p in itertools.permutations(range(n)):
        t=tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in edges))
        if best is None or t<best: best=t
    return best
def inv(n,edges):
    deg=[0]*n
    for a,b in edges: deg[a]+=1; deg[b]+=1
    return tuple(sorted(deg))
if __name__=='__main__':
    t0=time.time(); res={'files':sys.argv[1:],'laman':0,'free':[],'free_no_adjacent_copy':[]}
    for f in sys.argv[1:]:
        for line in open(f):
            n,adj=parse(line)
            if sum(bin(a).count('1') for a in adj)//2!=2*n-3: continue
            if min(bin(a).count('1') for a in adj)<3: continue
            lam,fr=laman_free(n,adj)
            if not lam: continue
            res['laman']+=1
            if not fr: continue
            g=line.strip(); res['free'].append(g)
            edges=[(a,b) for a in range(n) for b in range(a+1,n) if (adj[a]>>b)&1]
            non=[(a,b) for a in range(n) for b in range(a+1,n) if not (adj[a]>>b)&1]
            c0=canon(n,edges); d0=inv(n,edges); bad=False
            for e in edges:
                for fe in non:
                    E2=[x for x in edges if x!=e]+[fe]
                    if inv(n,E2)!=d0: continue
                    if canon(n,E2)==c0: bad=True; break
                if bad: break
            if not bad: res['free_no_adjacent_copy'].append(g)
    res['secs']=round(time.time()-t0,1); print(json.dumps(res))

# MathDB 341596 / Lu-Wang Conjecture 6: every simple k-uniform covering hypergraph (k>=4) on n vertices
# with m>=3 edges has a Berge cycle C_s for every 3<=s<=min(m,n).
# Usage: berge.py k n mlo mhi [all|fix]   ('fix' = WLOG first edge is {0..k-1}; valid by symmetry)
import sys,itertools,time,json
k,n,mlo,mhi=map(int,sys.argv[1:5]); mode=sys.argv[5] if len(sys.argv)>5 else 'fix'
E=[sum(1<<v for v in c) for c in itertools.combinations(range(n),k)]
pairs=[(1<<a)|(1<<b) for a in range(n) for b in range(a+1,n)]
def covering(F):
    return all(any(p&e==p for e in F) for p in pairs)
def has_cycle(F,s):
    m=len(F)
    # DFS: vertices v1<all others in cycle (rotation symmetry), edges used bitmask
    def dfs(start,cur,vused,eused,length):
        if length==s:
            for i in range(m):
                if not eused>>i&1 and F[i]>>start&1 and F[i]>>cur&1: return True
            return False
        for i in range(m):
            if eused>>i&1 or not F[i]>>cur&1: continue
            e=F[i]
            w=e & ~vused & ~((1<<(start+1))-1)
            while w:
                b=w&-w; w^=b; v=b.bit_length()-1
                if dfs(start,v,vused|b,eused|(1<<i),length+1): return True
        return False
    for st in range(n):
        if dfs(st,st,1<<st,0,1): return True
    return False
t0=time.time(); stats={}; bad=[]
for m in range(mlo,mhi+1):
    cnt=cov=0
    if mode=='fix':
        it=((E[0],)+c for c in itertools.combinations(E[1:],m-1))
    else:
        it=itertools.combinations(E,m)
    for F in it:
        cnt+=1
        if not covering(F): continue
        cov+=1
        for s in range(3,min(m,n)+1):
            if not has_cycle(list(F),s):
                bad.append(dict(m=m,s=s,edges=[[v for v in range(n) if e>>v&1] for e in F])); break
        if len(bad)>=5: break
    stats[m]=dict(families=cnt,covering=cov)
    print(json.dumps(dict(k=k,n=n,m=m,mode=mode,families=cnt,covering=cov,bad=len(bad),t=round(time.time()-t0,1))),flush=True)
    if len(bad)>=5: break
print('BAD',json.dumps(bad[:5]))

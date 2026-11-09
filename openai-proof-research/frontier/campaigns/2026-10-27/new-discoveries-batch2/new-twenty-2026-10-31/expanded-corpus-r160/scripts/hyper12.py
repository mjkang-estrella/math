# Twin-free 3-uniform hypergraphs: does a {1,2} edge weighting exist with no edge having all 3 weighted degrees equal?
import sys,itertools,random,time
def twin_free(n,E):
    inc=[0]*n
    for k,e in enumerate(E):
        for v in e: inc[v]|=1<<k
    used=[v for v in range(n) if inc[v]]
    return len(set(inc[v] for v in used))==len(used), inc
def has12(n,E):
    m=len(E)
    # backtracking: assign weights edge by edge; check an edge once all edges touching its vertices are assigned
    inc=[[] for _ in range(n)]
    for k,e in enumerate(E):
        for v in e: inc[v].append(k)
    last=[max(inc[v]) if inc[v] else -1 for v in range(n)]
    # edge k becomes checkable at step max(last[v] for v in e)
    check_at=[[] for _ in range(m)]
    for k,e in enumerate(E): check_at[max(last[v] for v in e)].append(k)
    w=[0]*m; deg=[0]*n
    def rec(k):
        if k==m: return True
        for val in (1,2):
            w[k]=val
            for v in E[k]: deg[v]+=val
            ok=all(not(deg[a]==deg[b]==deg[c]) for (a,b,c) in (E[j] for j in check_at[k]))
            if ok and rec(k+1): return True
            for v in E[k]: deg[v]-=val
        return False
    return rec(0)
if __name__=='__main__':
    mode=sys.argv[1]
    t=time.time(); bad=[]; cnt=0
    if mode=='exh':
        n=int(sys.argv[2]); trip=list(itertools.combinations(range(n),3)); M=len(trip)
        lo=int(sys.argv[3]); hi=int(sys.argv[4])
        for mask in range(lo,min(hi,1<<M)):
            E=[trip[i] for i in range(M) if mask>>i&1]
            if not E: continue
            tf,_=twin_free(n,E)
            if not tf: continue
            cnt+=1
            if not has12(n,E): bad.append(E)
    else:
        n=int(sys.argv[2]); trials=int(sys.argv[3]); rnd=random.Random(int(sys.argv[4]))
        trip=list(itertools.combinations(range(n),3))
        for _ in range(trials):
            p=rnd.random()
            E=[e for e in trip if rnd.random()<p]
            if not E: continue
            tf,_=twin_free(n,E)
            if not tf: continue
            cnt+=1
            if not has12(n,E): bad.append(E)
    print(mode,sys.argv[2:],'twin-free tested',cnt,'no {1,2}-weighting',len(bad),'examples',bad[:3],'sec',round(time.time()-t,1))

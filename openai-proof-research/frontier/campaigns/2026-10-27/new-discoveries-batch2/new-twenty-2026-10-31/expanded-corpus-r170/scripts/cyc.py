# Does G have a cyclic interval t-colouring (proper, all t colours used, each vertex's colours form a cyclic interval of Z_t)?
import sys,time
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from dp_sweep_lib import parse
def span_ok(cols,t,dg):
    if len(cols)<=1: return True
    s=sorted(cols); gap=max((s[(i+1)%len(s)]-s[i])%t for i in range(len(s)))
    return t-gap+1<=dg
def has_cyc(adj,t,limit=int(__import__("os").environ.get("CYCLIM","2000000"))):
    n=len(adj); deg=[len(a) for a in adj]
    if max(deg)>t: return False
    # edge order: DFS over vertices by degree
    order=[];seen=set();vs=[max(range(n),key=lambda v:deg[v])];vis={vs[0]}
    i=0
    while i<len(vs):
        v=vs[i];i+=1
        for w in sorted(adj[v],key=lambda w:-deg[w]):
            e=(min(v,w),max(v,w))
            if e not in seen: seen.add(e);order.append(e)
            if w not in vis: vis.add(w);vs.append(w)
    m=len(order)
    if m<t: return False
    cols=[set() for _ in range(n)]; used=[0]*t; nused=[0]; nodes=[0]
    def rec(i):
        nodes[0]+=1
        if nodes[0]>limit: raise TimeoutError
        if i==m: return nused[0]==t
        if t-nused[0]>m-i: return False
        a,b=order[i]
        rng=[0] if i==0 else range(t)
        for c in rng:
            if c in cols[a] or c in cols[b]: continue
            cols[a].add(c);cols[b].add(c)
            if span_ok(cols[a],t,deg[a]) and span_ok(cols[b],t,deg[b]):
                if used[c]==0: nused[0]+=1
                used[c]+=1
                if rec(i+1): return True
                used[c]-=1
                if used[c]==0: nused[0]-=1
            cols[a].discard(c);cols[b].discard(c)
        return False
    return rec(0)
def tri_free(adj):
    S=[set(a) for a in adj]
    return not any(S[u]&S[w] for u in range(len(adj)) for w in adj[u] if w>u)
if __name__=='__main__':
    n=int(sys.argv[1]); mode=sys.argv[2]; start=int(sys.argv[3]); cnt=int(sys.argv[4])
    lines=open(f'sources/graphdata/graph{n}c.g6').read().split()
    t0=time.time(); tested=0; to=0; hits=0
    for idx in range(start,min(len(lines),start+cnt)):
        adj=parse(lines[idx]); m=sum(map(len,adj))//2; D=max(map(len,adj))
        if mode=='i':
            if not tri_free(adj) or D<5: continue
            bound=n; tmax=min(m,n+D-3)
        else:
            bound=2*n-3; tmax=min(m,2*n+D-5)
        if tmax<=bound: continue
        tested+=1
        for t in range(bound+1,tmax+1):
            try:
                if has_cyc(adj,t): hits+=1; print('HIT',mode,idx,lines[idx],'t',t,flush=True); break
            except TimeoutError: to+=1; print('TO',idx,lines[idx],t,flush=True)
        if time.time()-t0>110: print('timecap at',idx);break
    print('n',n,mode,'range',start,start+cnt,'tested',tested,'timeouts',to,'hits',hits,round(time.time()-t0,1))

# Exhaustive/sharded check of Linusson-Potka Conjecture 4.3 for SYT(sc_n), optimized:
# memoized EG insertion on tuple tableaux, per-Q memoized completion sets, BFS for unit chains.
import sys, time, json
sys.setrecursionlimit(10000)
_ins={}
def insert(P,x):
    key=(P,x); r=_ins.get(key)
    if r is not None: return r
    rows=[list(t) for t in P]; i=0
    while True:
        if i==len(rows): rows.append([x]); break
        row=rows[i]
        if x>row[-1]: row.append(x); break
        if x in row: x=x+1; i+=1; continue
        k=next(t for t,z in enumerate(row) if z>x); z=row[k]; row[k]=x; x=z; i+=1
    r=(tuple(tuple(t) for t in rows),i); _ins[key]=r; return r
def frozen(P): return all(P[i][j]==i+j+1 for i in range(len(P)) for j in range(len(P[i])))
def syt_iter(n):
    shape=list(range(n-1,0,-1)); N=sum(shape); rows=[[] for _ in shape]
    def rec(k):
        if k>N: yield tuple(tuple(r) for r in rows); return
        for i in range(len(shape)):
            if len(rows[i])<shape[i] and (i==0 or len(rows[i-1])>len(rows[i])):
                rows[i].append(k); yield from rec(k+1); rows[i].pop()
    yield from rec(1)
def colword(Q,N):
    c=[0]*N
    for i,r in enumerate(Q):
        for j,v in enumerate(r): c[v-1]=j+1
    return tuple(c)
def promotion_inverse(Q,N):
    T={(i,j):Q[i][j] for i in range(len(Q)) for j in range(len(Q[i]))}; js=[]
    for k in range(N):
        live={c:v for c,v in T.items() if v is not None}
        (i,j)=max(live,key=lambda c:live[c]); js.append(j+1); path=[(i,j)]
        while True:
            a,b=path[-1]; cand=[(T[c],c) for c in ((a,b-1),(a-1,b)) if c in T and T[c] is not None]
            if not cand: break
            path.append(max(cand)[1])
        for t in range(len(path)-1): T[path[t]]=T[path[t+1]]
        T[path[-1]]=None
    return tuple(reversed(js))
def W_Q(Q,N,n):
    rowof=[0]*(N+2)
    for i,r in enumerate(Q):
        for v in r: rowof[v]=i
    memo={}
    def comp(P,k):
        key=(P,k)
        if key in memo: return memo[key]
        if k==N: res=[()] if frozen(P) else []
        else:
            res=[]
            for x in range(1,n):
                P2,i=insert(P,x)
                if i==rowof[k+1]:
                    for s in comp(P2,k+1): res.append((x,)+s)
        memo[key]=res; return res
    return comp((),0)
def check(Q,N,n):
    u=promotion_inverse(Q,N); c=colword(Q,N); W=W_Q(Q,N,n); S=set(W)
    if u not in S or c not in S: return dict(error=True,u=u,c=c)
    maximal=not any(w!=u and all(a<=b for a,b in zip(u,w)) for w in W)
    # BFS by unit increments inside S from c, staying <= u
    seen={c}; stack=[c]; reach=False
    while stack:
        w=stack.pop()
        if w==u: reach=True; break
        for t in range(N):
            if w[t]<u[t]:
                v=w[:t]+(w[t]+1,)+w[t+1:]
                if v in S and v not in seen: seen.add(v); stack.append(v)
    return dict(maximal=maximal,unitchain=reach,size=len(W),ell_upper=sum(a-b for a,b in zip(u,c)))
if __name__=='__main__':
    n=int(sys.argv[1]); start=int(sys.argv[2]); stop=int(sys.argv[3]); out=sys.argv[4]
    N=n*(n-1)//2; t0=time.time(); done=0; bad=[]; mx=0; last=start-1
    for idx,Q in enumerate(syt_iter(n)):
        if idx<start: continue
        if idx>=stop or time.time()-t0>105: break
        r=check(Q,N,n); done+=1; last=idx; mx=max(mx,r.get('size',0))
        if r.get('error') or not r['maximal'] or not r['unitchain']: bad.append((idx,Q,r)); print('FAIL',idx,Q,r,flush=True)
    rec=dict(n=n,start=start,last_index_checked=last,checked=done,max_WQ=mx,failures=bad,seconds=time.time()-t0,insert_memo=len(_ins))
    json.dump(rec,open(out,'w')); print(json.dumps(rec)[:500],flush=True)

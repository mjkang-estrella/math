# Function-form, count-based construction search for HJ(k,2)>=k  (i.e. a valid colouring of [k]^(k-1)).
# Blue set B = {(u,y): y = g(N(u))}, u in [k]^(k-2), N(u) = letter-count vector (composition of m=k-2 into k parts).
# Valid iff for every composition c and d>=1 with |c|+d=m, the tuple pi(j)=g(c+d e_j) is a permutation
# of [k] having >=1 fixed point and no two fixed points j, j+1.
import sys,time,json,random
def comps(n,k):
    if k==1: yield (n,); return
    for i in range(n+1):
        for r in comps(n-i,k-1): yield (i,)+r
def build(k):
    m=k-2; V=list(comps(m,k)); idx={v:i for i,v in enumerate(V)}; C=[]
    for d in range(1,m+1):
        for c in comps(m-d,k):
            t=[]
            for j in range(k):
                w=list(c); w[j]+=d; t.append(idx[tuple(w)])
            C.append(t)
    return V,C
def check_tuple(vals,k):
    if sorted(vals)!=list(range(k)): return False
    fx=[vals[j]==j for j in range(k)]
    return any(fx) and not any(fx[j] and fx[j+1] for j in range(k-1))
def solve(k,limit,seed):
    V,C=build(k); N=len(V); FULL=(1<<k)-1
    cons_of=[[] for _ in range(N)]
    for ci,t in enumerate(C):
        for pos,x in enumerate(t): cons_of[x].append((ci,pos))
    dom=[FULL]*N; rnd=random.Random(seed); t0=time.time(); nodes=[0]; trail=[]
    def setdom(x,nd):
        if nd==dom[x]: return True
        if nd==0: return False
        trail.append((x,dom[x])); dom[x]=nd; return True
    def cons_ok(ci):
        t=C[ci]
        # all-different propagation (singletons) + hidden singles + fixed point feasibility
        changed=True
        while changed:
            changed=False
            for p,x in enumerate(t):
                dm=dom[x]
                if dm&(dm-1)==0:
                    for q,y in enumerate(t):
                        if q!=p and dom[y]&dm:
                            if not setdom(y,dom[y]&~dm): return False
                            changed=True
            union=0
            for x in t: union|=dom[x]
            if union!=FULL: return False
            for v in range(k):
                b=1<<v; holders=[x for x in t if dom[x]&b]
                if len(holders)==1 and dom[holders[0]]!=b:
                    if not setdom(holders[0],b): return False
                    changed=True
        # fixed point possible?
        poss=[bool(dom[t[j]]&(1<<j)) for j in range(k)]
        if not any(poss): return False
        sure=[dom[t[j]]==(1<<j) for j in range(k)]
        for j in range(k-1):
            if sure[j] and sure[j+1]: return False
            if sure[j] and dom[t[j+1]]&(1<<(j+1)):
                if not setdom(t[j+1],dom[t[j+1]]&~(1<<(j+1))): return False
            if sure[j+1] and dom[t[j]]&(1<<j):
                if not setdom(t[j],dom[t[j]]&~(1<<j)): return False
        if sum(poss)==1:
            j=poss.index(True)
            if not setdom(t[j],1<<j): return False
        return True
    def propagate(start):
        queue=list(start); seen=set()
        mark=len(trail)
        while queue:
            ci=queue.pop()
            before=len(trail)
            if not cons_ok(ci): return False
            for (x,_) in trail[before:]:
                for (cj,_) in cons_of[x]: queue.append(cj)
        return True
    def undo(mark):
        while len(trail)>mark:
            x,dm=trail.pop(); dom[x]=dm
    if not propagate(range(len(C))): return dict(k=k,result='root-infeasible')
    order=list(range(N)); rnd.shuffle(order)
    res={}
    def dfs():
        nodes[0]+=1
        if time.time()-t0>limit: res['timeout']=True; return True
        best=None;bc=99
        for x in order:
            dm=dom[x]
            if dm&(dm-1):
                c=bin(dm).count('1')
                if c<bc: bc=c;best=x
                if c==2: break
        if best is None:
            res['sol']=[(V[i],dom[i].bit_length()-1) for i in range(N)]; return True
        vals=[v for v in range(k) if dom[best]>>v&1]; rnd.shuffle(vals)
        for v in vals:
            mark=len(trail)
            setdom(best,1<<v)
            if propagate([ci for ci,_ in cons_of[best]]):
                if dfs(): return True
            undo(mark)
        return False
    dfs()
    out=dict(k=k,vars=N,constraints=len(C),nodes=nodes[0],secs=round(time.time()-t0,2),timeout=res.get('timeout',False))
    if 'sol' in res:
        g={v:val for v,val in res['sol']}
        ok=all(check_tuple([g[V[x]] for x in t],k) for t in C)
        out['verified']=ok; out['sol']=res['sol']
    else: out['found']=False
    return out
if __name__=='__main__':
    k=int(sys.argv[1]); lim=float(sys.argv[2]); seed=int(sys.argv[3])
    print(json.dumps(solve(k,lim,seed)))

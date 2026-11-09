# WalkSAT-style local search for count-based colourings (see hj_counts.py for the exact conditions).
import sys,random,time,json
sys.path.insert(0,__file__.rsplit('/',1)[0])
from hj_counts import build
def run(k,n,limit,seed,sym=False,noise=0.3,init=None):
    V,idx,cliques,stars=build(k,n); N=len(V); rnd=random.Random(seed)
    rep=list(range(N))
    if sym:
        for i,v in enumerate(V): rep[i]=min(i,idx[tuple(reversed(v))])
    # clauses: type 0 = at-least-one(star), type 1 = not both (pair)
    cl=[];
    for s in stars: cl.append((0,tuple(sorted(set(rep[x] for x in s)))))
    seenp=set()
    for g in cliques:
        for a in range(len(g)):
            for b in range(a+1,len(g)):
                x,y=rep[g[a]],rep[g[b]]
                if x==y: cl.append((2,(x,)))  # forces x red
                else:
                    key=(min(x,y),max(x,y))
                    if key not in seenp: seenp.add(key); cl.append((1,key))
    occ=[[] for _ in range(N)]
    for ci,(t,vs) in enumerate(cl):
        for x in vs: occ[x].append(ci)
    val=[0]*N
    for i in range(N):
        if rep[i]==i:
            if init is None: val[i]=1 if rnd.random()<0.15 else 0
            else: val[i]=1 if sum(j*V[i][j] for j in range(k))%k==init else 0
    def sat(ci):
        t,vs=cl[ci]
        if t==0: return any(val[x] for x in vs)
        if t==1: return not (val[vs[0]] and val[vs[1]])
        return not val[vs[0]]
    unsat=set(ci for ci in range(len(cl)) if not sat(ci)); init_unsat=len(unsat)
    w=[1]*len(cl)
    t0=time.time(); steps=0; best=len(unsat)
    def delta(x):
        # weighted change in unsat if flip x
        d=0
        val[x]^=1
        for ci in occ[x]:
            s=sat(ci)
            if s and ci in unsat: d-=w[ci]
            elif (not s) and ci not in unsat: d+=w[ci]
        val[x]^=1
        return d
    while unsat and time.time()-t0<limit:
        steps+=1
        ci=rnd.choice(tuple(unsat)) if steps%50==0 or len(unsat)<64 else next(iter(unsat))
        t,vs=cl[ci]
        cands=[x for x in vs if rep[x]==x]
        if rnd.random()<noise: x=rnd.choice(cands)
        else:
            ds=[(delta(x),rnd.random(),x) for x in cands]; x=min(ds)[2]
        val[x]^=1
        for cj in occ[x]:
            if sat(cj): unsat.discard(cj)
            else: unsat.add(cj)
        for cj in unsat: pass
        if steps%200==0:
            for cj in unsat: w[cj]+=1
        if len(unsat)<best: best=len(unsat)
    out=dict(k=k,n=n,sym=sym,seed=seed,init_unsat=init_unsat,steps=steps,secs=round(time.time()-t0,1),unsat=len(unsat),best=best)
    if not unsat:
        B=[V[i] for i in range(N) if val[rep[i]]]
        out['B']=B
    return out
if __name__=='__main__':
    k=int(sys.argv[1]); lim=float(sys.argv[2]); seed=int(sys.argv[3]); sym=len(sys.argv)>4 and sys.argv[4]=='sym'
    init=int(sys.argv[5]) if len(sys.argv)>5 else None
    r=run(k,k-1,lim,seed,sym,init=init); r['init']=init
    print(json.dumps(r))

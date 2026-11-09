# Exploratory (non-certificate) search for 338366 / BRT Conjecture 4.1, case (p,q)=(2,2) [and optional (2,3),(3,2)].
# Cayley graphs Cay(G,S) of permutation groups G=<S> <= S_n, right multiplication, S symmetric, 1 notin S.
# Sufficient curvature test (explicit plan): kappa_{1/2}(x,y) >= (d+1-M)/(2d), M = min assignment cost N(x)\N[y] -> N(y)\N[x].
# Condition used: M <= p*q+2p-3 on every edge orbit (edges {1,g}, g in S, suffice by vertex transitivity).
# Then BFS spheres from identity, compare with T_p^q sphere sizes. Output JSON lines of hits. Seeded, bounded.
import itertools,json,random,sys
from math import comb
def mul(u,v): return tuple(u[i] for i in v)   # (u*v)(i)=u(v(i))
def inv(u):
    r=[0]*len(u)
    for i,x in enumerate(u): r[x]=i
    return tuple(r)
def tree_spheres(p,q,R):
    s=[1]+[p*(p-1)**(m-1) for m in range(1,R+1)]
    out=[]
    for i in range(R+1):
        tot=0
        for c in itertools.product(range(i+1),repeat=q):
            if sum(c)==i:
                pr=1
                for x in c: pr*=s[x]
                tot+=pr
        out.append(tot)
    return out
def ball(S,e,r):
    L={e:0}; fr=[e]
    for k in range(1,r+1):
        nf=[]
        for h in fr:
            for s in S:
                g=mul(h,s)
                if g not in L: L[g]=k; nf.append(g)
        fr=nf
    return L
def Mcost(S,g,B3):
    e=tuple(range(len(g)))
    Nx=set(S); Ny={mul(g,s) for s in S}
    A=[a for a in Nx if a!=g and a not in Ny]; Bs=[b for b in Ny if b!=e and b not in Nx]
    def d(u,v): return B3.get(mul(inv(u),v),4)
    best=99
    for perm in itertools.permutations(Bs):
        c=sum(d(a,b) for a,b in zip(A,perm))
        if c<best: best=c
    return best
def spheres(S,e,cap):
    L={e:0}; fr=[e]; out=[1]
    while fr and len(L)<=cap:
        nf=[]
        for h in fr:
            for s in S:
                g=mul(h,s)
                if g not in L: L[g]=len(out); nf.append(g)
        if nf: out.append(len(nf))
        fr=nf
    return out,len(L)
def main():
    n=int(sys.argv[1]); trials=int(sys.argv[2]); seed=int(sys.argv[3]); p,q=int(sys.argv[4]),int(sys.argv[5])
    d=p*q; Mmax=p*q+2*p-3; T=tree_spheres(p,q,30)
    rng=random.Random(seed); e=tuple(range(n)); seen=set(); stats={'trials':0,'curv_ok':0,'hits':0}
    for t in range(trials):
        stats['trials']+=1
        k=rng.choice([0,1,2]) if d==4 else rng.choice(range(d//2+1))
        # k = number of non-involution generator pairs; rest involutions
        gens=[]
        for _ in range(k):
            a=list(range(n)); rng.shuffle(a); a=tuple(a)
            gens+= [a,inv(a)]
        while len(gens)<d:
            # random involution
            pts=list(range(n)); rng.shuffle(pts); a=list(range(n))
            m=rng.randint(1,n//2)
            for i in range(m): x,y=pts[2*i],pts[2*i+1]; a[x]=y; a[y]=x
            gens.append(tuple(a))
        S=gens
        if len(set(S))!=d or e in S or set(map(inv,S))!=set(S): continue
        B3=ball(S,e,3)
        if any(Mcost(S,g,B3)>Mmax for g in S): continue
        stats['curv_ok']+=1
        sp,order=spheres(S,e,200000)
        exc=[(i,sp[i],T[i]) for i in range(1,min(len(sp),len(T))) if sp[i]>T[i]]
        if exc:
            key=(order,tuple(sp))
            if key in seen: continue
            seen.add(key); stats['hits']+=1
            print(json.dumps({'n':n,'order':order,'spheres':sp,'tree':T[:len(sp)],'exceed':exc,'S':S,'M':[Mcost(S,g,B3) for g in S]}),flush=True)
            if stats['hits']>=5: break
    print(json.dumps({'stats':stats,'p':p,'q':q,'Mmax':Mmax}),flush=True)
main()

"""Exact finite checks of the NEW mechanisms; no asymptotic simulation."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from itertools import product, combinations
import json

def involutions(items):
    if not items:
        yield {}; return
    a,*rest=items
    for m in involutions(rest): yield dict(m,**{str(a):a})
    for b in rest:
        for m in involutions([x for x in rest if x!=b]):
            m=dict(m); m[str(a)]=b;m[str(b)]=a;yield m

def absorption():
    cases=0
    subsets=[{i for i in range(3) if mask>>i&1} for mask in range(8)]
    for raw in involutions(list(range(6))):
        T=[raw[str(i)] for i in range(6)]
        for A in subsets[1:]:
            r=max(F(sum(T[2*g+j]//2 not in A for j in range(2)),2) for g in A)
            TA=lambda a: T[a] if T[a]//2 in A else a
            assert sorted(TA(a) for a in range(6) if a//2 in A)==[a for a in range(6) if a//2 in A]
            if r==1: continue
            for U in subsets:
                for V in subsets:
                    if not U<=V:continue
                    e1=max([F(sum(T[2*g+j]//2 not in V for j in range(2)),2) for g in U&A]+[F(0)])
                    for W in subsets:
                        e2=max([F(sum(T[2*g+j]//2 not in W for j in range(2)),2) for g in V&A]+[F(0)])
                        p=F(len((U-W)&A),len(A))
                        assert (1-r)*p<=e1+e2
                        cases+=1
    # A two-mark involution on three states: retrying accepted proposals biases law.
    Q=[[F(1,2),F(1,2)],[F(1),F(0)]]
    output=[sum(F(1,2)*Q[i][j] for i in range(2)) for j in range(2)]
    assert output==[F(3,4),F(1,4)]
    return dict(exhaustive_absorption_instances=cases,retry_output=list(map(str,output)),retry_stationary=['2/3','1/3'])

def cube(offset=0):
    return {tuple(sorted((offset+i,offset+(i^(1<<b))))) for i in range(8) for b in range(3)}
def adj(edges):
    a={v:set() for e in edges for v in e}
    for v,w in edges:a[v].add(w);a[w].add(v)
    return a
def girth(edges):
    a=adj(edges);best=len(a)+1
    for root in a:
        dist={root:0};parent={root:None};queue=[root]
        for v in queue:
            for w in a[v]:
                if w not in dist:dist[w]=dist[v]+1;parent[w]=v;queue.append(w)
                elif parent[v]!=w:best=min(best,dist[v]+dist[w]+1)
    return best
def boundary_switch(E,pending,far,mask):
    out=set(E);revfar=list(far)
    for i,((p,t),(u,v)) in enumerate(zip(pending,far)):
        if not(mask>>i&1):continue
        out.remove(tuple(sorted((p,t))));out.remove(tuple(sorted((u,v))))
        out.add(tuple(sorted((p,u))));out.add(tuple(sorted((t,v))))
        revfar[i]=(t,v)
    newpending=[(p,far[i][0]) if mask>>i&1 else (p,t) for i,(p,t) in enumerate(pending)]
    return out,newpending,revfar
def graph_checks():
    # Two simultaneous rooted one-level explorations, six independent exterior groups.
    E=set().union(*(cube(8*i) for i in range(8)))
    pending=[(r,r+t) for r in (0,8) for t in (1,2,4)]
    far=[(16+8*i,17+8*i) for i in range(6)]
    counts=[]
    for mask in range(64):
        out,p2,f2=boundary_switch(E,pending,far,mask)
        back,_,_=boundary_switch(out,p2,f2,mask)
        assert back==E and all(len(x)==3 for x in adj(out).values())
        assert girth(out)>3;counts.append(girth(out))
    # Independent trace computation checks the finite-walk anchor up to g=3.
    a=adj(cube());walks=[]
    for k in range(5):
        total=0
        for v in a:
            row={v:1}
            for _ in range(k):
                new={x:0 for x in a}
                for x,c in row.items():
                    for y in a[x]:new[y]+=c
                row=new
            total+=row.get(v,0)
        walks.append(F(total,8))
    assert walks[:4]==[1,0,3,0] and walks[4]==21 # tree fourth moment is 15.
    return dict(two_base_subsets=64,girth_min=min(counts),walk_moments=list(map(str,walks)),tree_fourth_moment=15)

def matrix_checks():
    E=cube();found=None
    for (a,b),(c,d) in combinations(sorted(E),2):
        if len({a,b,c,d})<4:continue
        new=(E-{(a,b),(c,d)})|{tuple(sorted((a,d))),tuple(sorted((c,b)))}
        if len(new)==len(E) and all(len(x)==3 for x in adj(new).values()) and girth(new)>3 and new!=E:
            found=(a,b,c,d,new);break
    assert found
    a,b,c,d,new=found
    def matrix(edges):
        H=[[F(i-3,11)-10 if i==j else F(0) for j in range(8)] for i in range(8)]
        for i,j in edges:H[i][j]=H[j][i]=F(1)
        return H
    def inv(M):
        n=len(M);A=[list(row)+[F(i==j) for j in range(n)] for i,row in enumerate(M)]
        for i in range(n):
            k=next(k for k in range(i,n) if A[k][i]);A[i],A[k]=A[k],A[i]
            scale=A[i][i];A[i]=[x/scale for x in A[i]]
            for j in range(n):
                if j!=i:
                    scale=A[j][i];A[j]=[x-scale*y for x,y in zip(A[j],A[i])]
        return [row[n:] for row in A]
    def mul(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
    H=matrix(E);Hp=matrix(new);R=inv(H);Rp=inv(Hp)
    B=[[Hp[i][j]-H[i][j] for j in range(8)] for i in range(8)]
    RB=mul(mul(R,B),Rp)
    assert all(Rp[i][j]-R[i][j]+RB[i][j]==0 for i in range(8) for j in range(8))
    cut=E-{tuple(sorted((a,b))),tuple(sorted((c,d)))}
    cutnew=new-{tuple(sorted((a,d))),tuple(sorted((c,b)))}
    assert cut==cutnew
    # Graph-only involution leaves each of 16 endpoint potential assignments fixed.
    atoms={(g,v):F(1,32) for g in range(2) for v in product((-1,1),repeat=4)}
    pushed={(1-g,v):p for (g,v),p in atoms.items()};assert pushed==atoms
    return dict(cube_switch=[a,b,c,d],woodbury_exact=True,double_cut_identical=True,potential_product_atoms=len(atoms))

def run(): return {'absorption':absorption(),'graphs':graph_checks(),'matrices':matrix_checks(),'scope':'Exact finite checks only; not analytic correctness or significance.'}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))

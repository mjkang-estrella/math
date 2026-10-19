"""Original exact finite diagnostics; no all-order or full stacked-matrix certificate."""
import json, math
from fractions import Fraction
import random

def test(m):
    n=2*m+1;r=2*m;rho=Fraction(1,10);M0=100000
    s=lambda i:1+i
    t=lambda i:1+m+i
    arcs=[]
    for i in range(m):
        for j in range(m):
            if i!=j:
                for copy in range(2):arcs.append((s(i),s(j),M0,'inner',i,j,copy))
    for i in range(m):
        for copy in range(m):arcs.append((0,t(i),Fraction(m-2,m),'root',i,i,copy))
        for copy in range(m):arcs.append((s(i),t(i),Fraction(m,m+2),'out',i,i,copy))
        for copy in range(2):arcs.append((t(i),s(i),Fraction(m,m+2),'in',i,i,copy))
    assert len(arcs)==r*(n-1)
    indeg=[sum(v==x for u,v,*_ in arcs) for x in range(n)]
    assert indeg==[0]+[r]*(n-1)
    # Build explicit disjoint directed packing described in the proof.
    Q=[]
    for i in range(m):
        mandatory=[2*i,2*i+1]
        Q.append(set(mandatory+[j for j in range(r) if j not in mandatory][:m-2]))
    assignments=[[] for j in range(r)]
    for u,v,w,kind,i,j,c in arcs:
        if kind=='inner':idx=2*i+c
        elif kind=='in':idx=2*i+c
        elif kind=='root':idx=sorted(Q[i])[c]
        else:idx=sorted(set(range(r))-Q[i])[c]
        assignments[idx].append((u,v))
    for tr in assignments:
        assert len(tr)==n-1
        seen={0}
        while True:
            new=seen|{v for u,v in tr if u in seen}
            if new==seen:break
            seen=new
        assert len(seen)==n
        assert [sum(v==x for u,v in tr) for x in range(n)]==[0]+[1]*(n-1)
    # Full D mincuts checked only for m=3,5; proof handles every m.
    D=[(u,v) for u,v,*_ in arcs]
    for i in range(m):D.extend([(t(i),0)]*m+[(t(i),s(i))]*(m-2))
    assert all(sum(u==v0 for u,v in D)==sum(v==v0 for u,v in D) for v0 in range(n))
    cutmin=None
    if m<=5:
        cutmin=min(sum(((mask>>u)&1) and not((mask>>v)&1) for u,v in D) for mask in range(1,2**n-1))
        assert cutmin==r
    # Ground root 0; exact weighted effective-resistance arithmetic.
    L=[[Fraction(0) for j in range(n-1)] for i in range(n-1)]
    for u,v,w,*_ in arcs:
        w=Fraction(w)
        if u: L[u-1][u-1]+=w
        if v: L[v-1][v-1]+=w
        if u and v: L[u-1][v-1]-=w; L[v-1][u-1]-=w
    R=[row+[Fraction(i==j) for j in range(n-1)] for i,row in enumerate(L)]
    for col in range(n-1):
        pivot=next(i for i in range(col,n-1) if R[i][col])
        R[col],R[pivot]=R[pivot],R[col]
        c=R[col][col]; R[col]=[x/c for x in R[col]]
        for i in range(n-1):
            if i!=col:
                c=R[i][col]
                R[i]=[x-c*y for x,y in zip(R[i],R[col])]
    Inv=[row[n-1:] for row in R]
    def resistance(u,v):
        return (Inv[u-1][u-1] if u else 0)+(Inv[v-1][v-1] if v else 0)-(2*Inv[u-1][v-1] if u and v else 0)
    maxnorm=max(Fraction(w)*resistance(u,v) for u,v,w,*_ in arcs)
    assert maxnorm<=(1+rho)/r
    rng=random.Random(107+m)
    sgn={(i,j):bool(rng.getrandbits(1)) for i in range(m) for j in range(i+1,m)}
    selected=[]
    for u,v,w,kind,i,j,c in arcs:
        if kind=='inner':yes=sgn[min(i,j),max(i,j)]==(i<j)
        elif kind=='root':yes=c<(m-1)//2
        elif kind=='out':yes=c<(m+1)//2
        else:yes=False
        selected.append(yes)
    Aarcs=[(a[0],a[1]) for a,yes in zip(arcs,selected) if yes]
    assert not any(u not in range(1,m+1) and v in range(1,m+1) for u,v in Aarcs)
    # Exact contracted-link leverage identities.
    a=Fraction(m-2);b=Fraction(m)
    assert (a+b/m)/(a+b)==Fraction(1,2)
    assert (b+a/m)/(a+b)==Fraction(1,2)+Fraction(1,m)
    return {'m':m,'r':r,'vertices':n,'B_arcs':len(arcs),'packing_checked':True,'D_min_cut':cutmin,'max_z_norm_squared_exact':str(maxnorm),'full_stack_finite_test':False,'A_incoming_S':0}

if __name__=='__main__':
    print(json.dumps({'status':'exact finite diagnostics only; no finite full-stack test; general proof in frame-obstruction.md','cases':[test(m) for m in (3,5,9,17)]},indent=2))

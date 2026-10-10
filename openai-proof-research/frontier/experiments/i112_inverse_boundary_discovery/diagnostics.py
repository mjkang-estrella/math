"""Exact finite diagnostics only. No files, network, subprocesses or bytecode writes."""
from fractions import Fraction as F
import json

def add(a,b):
    c=dict(a)
    for k,v in b.items(): c[k]=c.get(k,F(0))+v
    return {k:v for k,v in c.items() if v}
def scale(a,c): return {k:v*c for k,v in a.items() if v*c}
def mul(a,b):
    c={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(x+y for x,y in zip(k,l));c[m]=c.get(m,F(0))+v*w
    return {k:v for k,v in c.items() if v}
def der(a,i):
    c={}
    for k,v in a.items():
        if k[i]:
            l=list(k);l[i]-=1;c[tuple(l)]=v*k[i]
    return c
def lap(a,n):
    c={}
    for i in range(n):c=add(c,der(der(a,i),i))
    return c
def div(v):
    c={}
    for i,a in enumerate(v):c=add(c,der(a,i))
    return c
def rank(a):
    a=[list(map(F,row)) for row in a];r=0
    if not a:return 0
    for j in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][j]),None)
        if p is None:continue
        a[r],a[p]=a[p],a[r];q=a[r][j];a[r]=[v/q for v in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                q=a[i][j];a[i]=[v-q*w for v,w in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r
def monomials(n,d):
    if n==0:return [()] if d>=0 else []
    return [(i,)+a for i in range(d+1) for a in monomials(n-1,d-i)]

def check():
    lifts=0
    for n in (2,3,4,5):
        z=(0,)*n;x=[]
        for i in range(n):
            e=list(z);e[i]=1;x.append({tuple(e):F(1)})
        r2={}
        for a in x:r2=add(r2,mul(a,a))
        pairs=[]
        for i in range(n):
            for j in range(n):
                a=[{} for _ in range(n)];a[i]=x[j]
                b=scale(mul(x[0],x[0]),F(1,2)) if i==j else {}
                pairs.append((a,b))
        for i in range(n):
            for j in range(i,n):
                if i==j:
                    if i==0:continue
                    b=scale(add(mul(x[i],x[i]),scale(mul(x[0],x[0]),-1)),F(1,2))
                else:b=mul(x[i],x[j])
                pairs.append(([{} for _ in range(n)],b))
        assert len(pairs)==n*n+n*(n+1)//2-1
        for a,b in pairs:
            assert div(a)==lap(b,n)
            v0=[scale(mul(r2,ai),F(1,2*n+4)) for ai in a]
            h=add(b,scale(div(v0),-1));assert not lap(h,n)
            v=[add(v0[i],scale(add(mul(x[i],h),scale(mul(r2,der(h,i)),F(-1,n+2))),F(n+2,n*(n+4)))) for i in range(n)]
            assert div(v)==b
            assert [lap(vi,n) for vi in v]==a
            lifts+=1
    # Dimension of unrestricted augmented 2-jets versus physical ones.
    n=3;mons=monomials(n,2);zero=(0,)*n
    columns=[];constraints=[]
    for c in range(4):
        for mon in mons:
            U=[{} for _ in range(4)];U[c]={mon:F(1)}
            u=U[:3];d=U[3];v=div(u)
            R=[add(scale(lap(u[i],3),3),scale(der(d,i),5)) for i in range(3)]
            S=scale(lap(d,3),8)
            equations=[p.get(zero,0) for p in R]+[S.get(zero,0)]
            physical=add(v,scale(d,-1))
            columns.append(equations)
            constraints.append(equations+[physical.get(zero,0)]+[der(physical,i).get(zero,0) for i in range(3)])
    augrank=rank(list(zip(*columns)));physrank=rank(list(zip(*constraints)))
    assert len(columns)==40 and augrank==4 and physrank==8
    # Only homogeneous Hessians, zero augmented lower jets.
    inds=[i for i in range(40) if sum(mons[i%10])==2]
    assert len(inds)==24
    hrank=rank([[row[i] for i in inds] for row in zip(*constraints)])
    assert hrank==7
    # Source state (0,1) is augmented harmonic, not physical.
    assert not lap({zero:F(1)},3)
    return {'cubic_basis_lifts':lifts,'augmented_2jet_dimension':40-augrank,
            'physical_2jet_dimension':40-physrank,'physical_zero_lower_jet_hessian_dimension':24-hrank,
            'status':'PASS finite exact checks; not universal proof certification'}

if __name__=='__main__':print(json.dumps(check(),indent=2))

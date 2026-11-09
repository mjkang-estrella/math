from pathlib import Path
from itertools import product, combinations
from collections import deque
import sympy as S
import random, json, datetime, hashlib, subprocess, urllib.request, urllib.error
O=Path(__file__).resolve().parent
rng=random.Random(2173105)
results={}
def rows(n):
    e=[S.eye(n).row(i) for i in range(n)]
    return list({tuple(e[i]+e[j]-e[k]) for i,j,k in product(range(n),repeat=3)})
total=0
for n in range(1,4):
    rr=rows(n)
    for d in range(1,n+1):
        for rs in combinations(rr,d):
            for cs in combinations(range(n),d):
                assert abs(S.Matrix(rs)[:,list(cs)].det())<=2**d
                total+=1
results['exhaustive_distinct_additive_row_minors_n_le_3']=total
# Repeated matrix rows have determinant zero; index repetitions occur in rows().
def forms(n):
    return [(tuple(S.eye(n).row(i)),S.Integer(-1)) for i in range(n)]+[(r,S.Integer(0)) for r in rows(n)]
vertices=0
for n in range(1,4):
    ff=forms(n)
    for fs in combinations(ff,n):
        a=S.Matrix([f[0] for f in fs]);b=S.Matrix([-f[1] for f in fs])
        if a.det():
            z=a.inv()*b
            assert max(map(abs,z))<=2**(n-1)
            vertices+=1
results['all_arrangement_vertex_bases_n_le_3']=vertices
def split(p,ff,depth=0):
    n=len(p); active=[list(a) for a,b in ff if (S.Matrix([a])*p)[0]+b==0]
    A=S.Matrix(active) if active else S.zeros(0,n)
    if A.rank()==n:return p,S.zeros(n,1)
    u=A.nullspace()[0];lo=None;hi=None
    for a,b in ff:
        v=(S.Matrix([a])*p)[0]+b;w=(S.Matrix([a])*u)[0]
        if w>0:lo=max(lo,-v/w) if lo is not None else -v/w
        if w<0:hi=min(hi,-v/w) if hi is not None else -v/w
    assert lo is not None or hi is not None
    assert depth<n
    if lo is None:
        z,r=split(p+hi*u,ff,depth+1);return z,r-hi*u
    if hi is None:
        z,r=split(p+lo*u,ff,depth+1);return z,r-lo*u
    assert lo<0<hi
    z1,r1=split(p+lo*u,ff,depth+1);z2,r2=split(p+hi*u,ff,depth+1)
    t=hi/(hi-lo);return t*z1+(1-t)*z2,t*r1+(1-t)*r2
samples=0;zeros=0
for n in range(1,4):
    points=[S.zeros(n,1),S.ones(n,1),S.Matrix([2**i for i in range(n)])]
    points += [S.Matrix([S.Rational(rng.randint(-50,50),rng.randint(1,7)) for _ in range(n)]) for _ in range(12)]
    for x in points:
        ff=forms(n);signed=[]
        for a,b in ff:
            v=(S.Matrix([a])*x)[0]+b;s=1 if v>=0 else -1
            signed.append((tuple(s*t for t in a),s*b))
        z,r=split(x,signed);assert z+r==x
        assert max(map(abs,z))<=2**(n-1)
        for a,b in signed:
            az=(S.Matrix([a])*z)[0]+b;ar=(S.Matrix([a])*r)[0]
            assert az>=0 and ar>=0
        for a,b in ff:
            vx=(S.Matrix([a])*x)[0]+b;vz=(S.Matrix([a])*z)[0]+b
            assert abs(vz)<=abs(vx)
            if vx==0:assert vz==0;zeros+=1
        samples+=1
results['exact_cell_decompositions']=samples;results['zero_residuals_preserved']=zeros
# Independent constructive proof control for the sign-free integer theorem.
tested=0;square=0
for trial in range(150):
    m=rng.randint(1,3);n=rng.randint(m,4)
    A=S.Matrix(m,n,[rng.randint(-3,3) for _ in range(m*n)])
    if A.rank()!=m:continue
    basis=next(cs for cs in combinations(range(n),m) if A[:,list(cs)].det())
    rest=[i for i in range(n) if i not in basis]
    B=A[:,list(basis)];delta=abs(int(B.det()));adj=B.adjugate()
    w=S.Matrix([rng.randint(-8,8) for _ in range(n)]);b=A*w
    residue=lambda v:tuple(int(t)%delta for t in adj*v)
    target=residue(b);start=(0,)*m;q=deque([start]);paths={start:[]}
    while target not in paths:
        v=q.popleft()
        for j in rest:
            g=residue(A[:,j]);v2=tuple((v[i]+g[i])%delta for i in range(m))
            if v2 not in paths:paths[v2]=paths[v]+[j];q.append(v2)
    path=paths[target];assert len(path)<=delta-1
    z=S.zeros(n,1)
    for j in path:z[j]+=1
    zb=B.inv()*(b-A*z)
    for i,j in enumerate(basis):z[j]=zb[i]
    assert A*z==b and all(t.q==1 for t in z)
    aug=A.row_join(b);Y=max(abs(aug[:,list(cs)].det()) for cs in combinations(range(n+1),m))
    assert max(map(abs,z))<=Y
    tested+=1;square+=int(m==n)
results['constructive_BFRT_cases']=tested;results['square_cases_Cramer']=square
results['limits']='Exact finite controls only; not a universal proof or independent certification of failed-run checks.'
(O/'check-results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results))

#!/usr/bin/env python3
import os, resource
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
import json, datetime
from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
r,n=6,4
chain=[(4,0,0,0,0,0),(4,4,3,0,0,0),(4,4,4,2,1,0),(4,4,4,4,3,2),(4,4,4,4,4,3),(4,4,4,4,4,4)]

def layer(mu,nu):
    cells=[(i,j) for i in range(r) for j in range(mu[i],nu[i])]
    counts=[0,0,0]; tab={}
    def go(pos,res):
        if pos==len(cells):counts[res]+=1;return
        i,j=cells[pos]
        for x in (1,2):
            if (i,j-1) in tab and x<tab[i,j-1]:continue
            if (i-1,j) in tab and x<=tab[i-1,j]:continue
            tab[i,j]=x;go(pos+1,(res+x)%3);del tab[i,j]
    go(0,0)
    doubles=0;free=[0]*r
    for j in range(n):
        rows=[i for i in range(r) if mu[i]<=j<nu[i]]
        assert len(rows)<=2
        if len(rows)==2:doubles+=1
        elif rows:free[rows[0]]+=1
    assert counts[1]==counts[2]
    factor=0 if any(x%3==2 for x in free) else (-1)**sum(x%3==1 for x in free)
    assert counts[0]-counts[1]==factor
    return {'mu':mu,'nu':nu,'counts':counts,'double_columns':doubles,'free_lengths':free,'specialized_sign':factor}
rows=[];mu=(0,)*r;total=[1,0,0]
for nu in chain:
    v=layer(mu,nu);rows.append(v)
    total=[sum(total[a]*v['counts'][b] for a in range(3) for b in range(3) if (a+b)%3==s) for s in range(3)]
    mu=nu
assert total==[426,427,427]
sizes=[sum(x) for x in chain]; profile=[sizes[0]]+[sizes[i]-sizes[i-1] for i in range(1,r)]
area=sum(i*v for i,v in enumerate(profile));assert area==46
# Aggregate this ONE content profile over all compatible shape chains.
parts=[tuple(reversed(x)) for x in combinations_with_replacement(range(n+1),r)]
def sign(mu,nu):
    free=[0]*r
    for j in range(n):
        rows=[i for i in range(r) if mu[i]<=j<nu[i]]
        if len(rows)>2:return 0
        if len(rows)==1:free[rows[0]]+=1
    return 0 if any(x%3==2 for x in free) else (-1)**sum(x%3==1 for x in free)
dp={(0,)*r:1}
for l,size in enumerate(sizes):
    nd={}
    for nu in parts:
        if sum(nu)!=size or nu[l]!=n:continue
        v=sum(c*sign(mu,nu) for mu,c in dp.items() if all(a<=b for a,b in zip(mu,nu)))
        if v:nd[nu]=v
    dp=nd
profile_coefficient=dp.get((n,)*r,0);assert profile_coefficient==0
# Independent symbolic check of coefficient formula and flagged determinant on one shape.
import sympy as s
x,t=s.symbols('x t'); f=[s.Integer(1),x-1]
for h in range(1,5):f.append(s.expand((t**h*x-1)*f[-1]-f[-2]))
def H(i,d):
    if d<0:return s.Integer(0)
    c=[s.Integer(0)]*(d+1);c[0]=s.Integer(1)
    for ell in range(i+1):
        # (1 + t^ell z + t^(2ell) z^2)^(-1)
        new=[]
        for j in range(d+1):new.append(s.expand(c[j]-(t**ell*new[j-1] if j>=1 else 0)-(t**(2*ell)*new[j-2] if j>=2 else 0)))
        c=new
    return c[d]
for m in range(6):
    for i in range(m+1):assert s.expand(f[m].coeff(x,i)-t**(i*(i-1)//2)*H(i,m-i))==0
R=2;N=2
D=s.det(s.Matrix([[H(i,N+j-i) for j in range(R)] for i in range(R)]))
res=Counter();a=[]
def tableaux(pos,degree,phase):
    if pos==R*N:res[degree,phase]+=1;return
    i,j=divmod(pos,N)
    lo=max(a[-1] if j else 1,a[pos-N]+1 if i else 1)
    for v in range(lo,2*(i+1)+1):
        a.append(v);tableaux(pos+1,degree+(v-1)//2,(phase+(1 if v%2 else 2))%3);a.pop()
tableaux(0,0,0)
poly=0
for d in set(k[0] for k in res):
    assert res[d,1]==res[d,2]
    poly+=(res[d,0]-res[d,1])*t**d
assert s.expand(poly-D)==0
out={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':{'address_space_MiB':512,'cpu_seconds':45,'threads':1},'negative_class':{'shape':[n]*r,'flags':list(range(2,2*r+1,2)),'chain':chain,'layers':rows,'residue_counts':total,'pair_content':profile,'area':area,'specialization':'-t^46'},'same_content_aggregated_coefficient':profile_coefficient,'coefficient_formula_checks':21,'single_flagged_identity_check':str(s.expand(D)),'status':'PASS; route obstruction only, not source refutation'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'residues':total,'area':area,'profile_coefficient':profile_coefficient}))

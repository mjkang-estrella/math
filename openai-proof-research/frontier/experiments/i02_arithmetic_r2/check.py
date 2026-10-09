"""Finite checks only: no inference of asymptotic density or novelty."""
from pathlib import Path
from fractions import Fraction as F
from math import prod, log
import subprocess, sys, json

ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
N=400000
spf=list(range(N+1))
for q in range(2,int(N**0.5)+1):
    if spf[q]==q:
        for n in range(q*q,N+1,q):
            if spf[n]==n: spf[n]=q
primes=[p for p in range(2,N+1) if spf[p]==p]
def fac(n):
    f={}
    while n>1:
        q=spf[n]; f[q]=f.get(q,0)+1; n//=q
    return f
def order(a,p,f):
    o=p-1
    for q in f:
        while o%q==0 and pow(a,o//q,p)==1: o//=q
    return o

reproduced=[]
for a in [2,-3,12]:
    r=subprocess.run([sys.executable,str(ROOT/'frontier/experiments/i02_arithmetic_index_decomposition_check.py'),str(a),'200000'],text=True,capture_output=True,check=True)
    reproduced.append(r.stdout.strip())
print('\n'.join(reproduced))

bases=[2,-2,3,-3,4,-4,8,-8,9,-9,12,-12,16,-16,27,-27,64,-64]
allrows=[]
small_checks=0
for x in [1000,10000,200000]:
    rows={a:dict(a=a,x=x,G=0,E1=0,E2=0,E3=0,good=0,violations=0) for a in bases}
    for p in primes:
        if not x<p<=2*x:continue
        f=fac(p-1); Q=max(f); m=(p-1)//Q
        for a in bases:
            if a%p==0:continue
            o=order(a,p,f); i=(p-1)//o
            if x==1000:
                v=1; direct=0
                while True:
                    direct+=1; v=(v*a)%p
                    if v==1:break
                assert direct==o
                small_checks+=1
            for q in f:
                assert (i%q==0)==(pow(a,(p-1)//q,p)==1)
            if Q**20<=x**13:continue
            r=rows[a];r['G']+=1
            assert m**20<2**20*x**7 and m%Q!=0
            assert all(q==Q or q**20<2**20*x**7 for q in fac(i))
            e1=i%Q==0
            e2=any(q>3 and q**20<2**20*x**7 and pow(a,(p-1)//q,p)==1 for q in f)
            e3=f.get(2,0)>=3 or f.get(3,0)>=2
            if e1:assert pow(a,m,p)==1
            for name,val in [('E1',e1),('E2',e2),('E3',e3)]:r[name]+=int(val)
            if not(e1 or e2 or e3):
                r['good']+=1
                if 12%i!=0:r['violations']+=1
    allrows.extend(rows.values())
assert all(r['violations']==0 for r in allrows)

units=[r for r in range(36) if r%2 and r%3]
union=F(sum(r%4==1 or r%9==1 for r in units),len(units))
assert union==F(7,12)<F(1,2)+F(1,6)
geometry=0
for j in range(13):
    for k in range(17):
        ell,b=F(j,60),F(k,64);h=(1+3*ell+b)/2
        assert 1-h/6+b/12==F(11,12)-ell/4
        geometry+=1
progressions=[]
for Y in [10,30,100,1000,10000]:
    # Base 2: p=5 (mod 8), and p !=1 (mod q) for odd q<=Y.
    qs=[q for q in primes if 2<q<=Y]
    density=F(1,4)*prod((F(q-2,q-1) for q in qs),start=F(1))
    log_phi=log(4)+sum(log(q-1) for q in qs)
    progressions.append(dict(Y=Y,union_density=float(density),log_phi_of_modulus=log_phi,integer_tail_bound=1/Y))
result=dict(warning='Finite logic only; theta=7/20 is not the theorem exponent.',original_reproductions=reproduced,independent_cases=allrows,direct_order_comparisons=small_checks,good_total=sum(r['good'] for r in allrows),violations=0,E3_union_exact=str(union),E3_sum_exact=str(F(2,3)),geometry_grid_checks=geometry,progression_mass_checks=progressions)
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['original_reproductions','independent_cases','progression_mass_checks']}))

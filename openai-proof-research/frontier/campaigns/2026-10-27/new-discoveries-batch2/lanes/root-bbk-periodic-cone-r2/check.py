import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[name]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
from fractions import Fraction
from pathlib import Path
import json,math
from itertools import product

def flag(r,p): return int((2*r+1)%p!=0)
def f(r): return int(len({flag(r,p) for p in (3,5,7)})==1)
P=[f(r) for r in range(105)]
assert P[0]==P[-1]==1 and P==P[::-1]
assert sum(P)==49

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y:c[i+j]+=x*y
    return c

def divexact(a,b):
    a=list(map(Fraction,a)); b=list(map(Fraction,b)); out=[Fraction(0)]*(len(a)-len(b)+1)
    for i in range(len(out)-1,-1,-1):
        v=a[i+len(b)-1]/b[-1];out[i]=v
        for j,w in enumerate(b):a[i+j]-=v*w
    assert not any(a)
    assert all(x.denominator==1 for x in out)
    return [int(x) for x in out]

# Pair-potential identity checked on every CRT class.
for r in range(105):
    a,b,c=[flag(r,p) for p in (3,5,7)]
    assert 2*f(r)==int(a==b)+int(b==c)+int(c==a)-1
    assert f(-1-r)==f(r)

# Every proper-period fibre needed by the allowed odd denominators meets a zero.
fibres={}
for d in range(1,36,2):
    g=math.gcd(d,105)
    witnesses=[]
    for a in range(g):
        r=next(r for r in range(a,105,g) if f(r)==0)
        witnesses.append(r)
    fibres[str(d)]={'gcd':g,'zero_witnesses':witnesses}

Q=[1]
for d in range(1,36,2): Q=mul(Q,[1]+[0]*(d-1)+[-1])
N0=divexact(mul(Q,P),[1]+[0]*104+[-1])
assert len(Q)-1==324 and len(N0)-1==323
assert N0[0]==1 and N0[-1]==-1
assert N0==[-x for x in N0[::-1]]
# H=(1+q^3570)F has the BBK(107,17) degree and reciprocal exponent.
N=mul(N0,[1]+[0]*3569+[1])
assert len(N)-1==17*(2*107+17-2)==3893
assert (len(N)-len(Q))==2*17*(107-2)-1==3569
assert N[0]==1 and N[-1]==-1
assert N==[-x for x in N[::-1]]
assert mul(N,[1]+[0]*104+[-1])==mul(mul(Q,P),[1]+[0]*3569+[1])
# Strengthen to strictly positive INTEGER coefficients and constant term 1.
# J=(1+q^3570)(3F+1/(1-q))-3+3q^3569.
Qdiv=divexact(Q,[1,-1])
base=[3*x for x in N0]
for i,x in enumerate(Qdiv):base[i]+=x
JN=mul(base,[1]+[0]*3569+[1])
for i,x in enumerate(Q):
    JN[i]-=3*x
    JN[i+3569]+=3*x
assert JN[0]==1 and JN[-1]==-1 and len(JN)-1==3893
assert JN==[-x for x in JN[::-1]]
representatives=[]
for binary in product((0,1),repeat=3):
    residues=[(p-1)//2 if bit==0 else 0 for p,bit in zip((3,5,7),binary)]
    r=next(r for r in range(105) if all(r%p==a for p,a in zip((3,5,7),residues)))
    y=-1 if len(set(binary))==1 else 1
    representatives.append({'binary':binary,'r':r,'y':y})
for d in range(1,36,2):
    g=math.gcd(d,105)
    for a in range(g):
        assert sum(t['y'] for t in representatives if t['r']%g==a)>=0
assert sum(t['y'] for t in representatives)==4
dual=sum(t['y']*(6*f(t['r'])+2) for t in representatives)
assert dual==-4
out={'status':'PASS','period':105,'mean_numerator':sum(P),'period_coefficients':P,
     'fibre_zero_witnesses':fibres,'base_cleared_numerator':N0,
     'matched_BBK_parameters':[107,17],'matched_degree':3893,'matched_D':3569,
     'shift':3570,'dual_representatives':representatives,'strict_example_dual_value':dual,
     'strict_example_constant':JN[0],'strict_example_leading':JN[-1],
     'scope':'Generic positive-fraction obstruction, NOT a BBK counterexample.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('period_coefficients','fibre_zero_witnesses','base_cleared_numerator')}))

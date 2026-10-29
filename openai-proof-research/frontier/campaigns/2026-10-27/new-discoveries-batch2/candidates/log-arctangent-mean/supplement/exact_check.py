#!/usr/bin/env python3
"""Independent finite-ring checker. No candidate code imported or executed."""
import os, resource, math, json, hashlib
from fractions import Fraction as F
from pathlib import Path
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','BLIS_NUM_THREADS'):
    os.environ[name]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
HERE=Path(__file__).resolve().parent
R=HERE.parent/'inputs/root-log-arctangent-certificate-r2'
O=HERE.parent/'inputs/root-log-arctangent-candidate-r1'
# Q[d]/(d^2-17); sparse maps (rational exponent coordinate, radical coordinate, t degree).
def q(a=0,b=0): return (F(a),F(b))
Z=q(); ONE=q(1)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def mul(x,y): return (x[0]*y[0]+17*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def powq(x,n):
    z=ONE
    for _ in range(n): z=mul(z,x)
    return z
def low(x): return x[0]+x[1]*(F(41,10) if x[1]>=0 else F(21,5))
def clean(p): return {k:v for k,v in p.items() if v!=Z}
def plus(*ps):
    r={}
    for p in ps:
        for k,v in p.items():r[k]=add(r.get(k,Z),v)
    return clean(r)
def scale(p,c):return clean({k:mul(v,c) for k,v in p.items()})
def product(p,r):
    z={}
    for (a,b,k),v in p.items():
        for (c,d,l),w in r.items():
            key=(a+c,b+d,k+l);z[key]=add(z.get(key,Z),mul(v,w))
    return clean(z)
def shift(p,n):return {(a,b,k+n):v for (a,b,k),v in p.items()}
def cs(a,b=0):return {(F(a),F(b),0):q(F(1,2)),(-F(a),-F(b),0):q(F(1,2))}
def sn(a,b=0):return {(F(a),F(b),0):q(F(1,2)),(-F(a),-F(b),0):q(-F(1,2))}
def deriv(p,n=1):
    # Direct Leibniz formula, rather than repeated derivative recurrence.
    z={}
    for (a,b,k),v in p.items():
        for j in range(min(k,n)+1):
            key=(a,b,k-j)
            coefficient=math.comb(n,j)*math.factorial(k)//math.factorial(k-j)
            w=mul(v,mul(q(coefficient),powq(q(a,b),n-j)))
            z[key]=add(z.get(key,Z),w)
    return clean(z)
def jet(p,n):
    return sumq([v for (a,b,k),v in deriv(p,n).items() if k==0])
def sumq(xs):
    r=Z
    for x in xs:r=add(r,x)
    return r
def enc(x):return [str(x[0]),str(x[1])]
def encode(p):return [{'exponent':enc((a,b)),'degree':k,'coefficient':enc(v)} for (a,b,k),v in sorted(p.items())]
# Build from the source-centered f' coth numerator, using half frequencies.
alpha=(F(5,2),F(1,2)); beta=(F(5,2),-F(1,2))
sa,sb=sn(*alpha),sn(*beta); ca,cb=cs(*alpha),cs(*beta)
B=product(product(sn(1),sa),sb)
A=plus(product(product(cs(1),sa),sb),scale(product(sn(1),plus(scale(product(ca,sb),alpha),scale(product(sa,cb),neg(beta)))),q(0,-F(1,17))))
A_display=scale(plus(cs(4),scale(product(cs(1),cs(0,1)),q(-1)),scale(product(sn(1),sn(0,1)),q(0,F(5,17)))),q(F(1,2)))
B_display=scale(product(sn(1),plus(cs(5),scale(cs(0,1),q(-1)))),q(F(1,2)))
assert A==A_display and B==B_display
# E directly from the numerator of (B/((1+2t^2)A))' - 1/(1+2t^2).
D=plus(A,scale(shift(A,2),q(2)))
E=plus(product(deriv(B),D),scale(product(B,deriv(D)),q(-1)),scale(plus(product(A,A),scale(shift(product(A,A),2),q(2))),q(-1)))
U=plus(product(deriv(B),A),scale(product(B,deriv(A)),q(-1)),scale(product(A,A),q(-1)))
V=scale(product(B,A),q(-4))
assert E==plus(U,shift(V,1),scale(shift(U,2),q(2)))
for p,sign in [(U,1),(V,-1)]:
    assert all(p.get((-a,-b,k),Z)==mul(q(sign),v) for (a,b,k),v in p.items())
assert all(E.get((-a,-b,k),Z)==mul(q((-1)**k),v) for (a,b,k),v in E.items())
# Compare only after reconstruction, never generating data from root table.
table=json.loads((O/'exponential-terms.json').read_text())
for name,p in [('U',U),('V',V)]:
    supplied={(F(r['lambda'][0]),F(r['lambda'][1]),0):tuple(map(F,r['coefficient'])) for r in table[name]}
    assert clean(supplied)==p
frequencies=[q(7,1),q(2,2),q(10),q(5,1),q(0,2),q(8),q(3,1),q(-2,2),q(7,-1),q(2),q(-3,1),q(5,-1)]
assert F(41,10)**2<17<F(21,5)**2
assert low(frequencies[-1])>0
assert all(low(add(x,neg(y)))>0 for x,y in zip(frequencies,frequencies[1:]))
assert {q(a,b) for a,b,k in U if low(q(a,b))>0}==set(frequencies)
assert {q(a,b) for a,b,k in V if low(q(a,b))>0}==set(frequencies)
assert all((a,b)==(0,0) or (q(a,b) in frequencies or neg(q(a,b)) in frequencies) for a,b,k in set(U)|set(V))
assert V.get((F(0),F(0),0),Z)==Z
zeroU=U.get((F(0),F(0),0),Z)
assert deriv({(F(0),F(0),0):zeroU,(F(0),F(0),2):mul(q(2),zeroU)},24)=={}
prefix=[Z,Z,Z];rows=[];target={};wrong94={}
for lam in frequencies:
    a,b=lam;u=U.get((a,b,0),Z);v=V.get((a,b,0),Z);l22=powq(lam,22)
    c0=mul(l22,sumq([mul(u,powq(lam,2)),mul(q(24),mul(v,lam)),mul(q(1104),u)]))
    c1=mul(l22,add(mul(v,lam),mul(q(94),u)));c2=mul(l22,mul(q(2),u))
    cs_=[c0,c1,c2];prefix=[add(x,y) for x,y in zip(prefix,cs_)]
    assert all(low(x)>0 for x in prefix)
    rows.append({'frequency':enc(lam),'u':enc(u),'v':enc(v),'c':list(map(enc,cs_)),'prefix':list(map(enc,prefix)),'lower_bounds':list(map(lambda x:str(low(x)),prefix))})
    # 2 cosh = exp+exp-, 2 sinh = exp-exp-; multiply both sides by 2.
    for sign in (1,-1):
        freq=(sign*a,sign*b)
        target[(*freq,0)]=c0
        target[(*freq,1)]=mul(q(sign),mul(add(c1,c2),lam))
        target[(*freq,2)]=mul(c2,powq(lam,2))
        wrong94[(*freq,0)]=c0
        wrong94[(*freq,1)]=mul(q(sign),mul(c1,lam))
        wrong94[(*freq,2)]=mul(c2,powq(lam,2))
assert deriv(E,24)==clean(target)
assert deriv(E,24)!=clean(wrong94) # adversarial 94-vs-96 mutation is detected
expected={10:37847040,12:19891322880,14:5550283554816,16:1162696473968640,18:206947471161556992,20:33226670114812723200,22:4978839848478924865536}
jets={str(n):enc(jet(E,n)) for n in range(24)}
assert all(jet(E,n)==q(expected.get(n,0)) for n in range(24))
root=json.loads((R/'checks.json').read_text())['success']
assert root['N']==24
assert len(root['rows'])==12
for own,given in zip(rows,root['rows']):
    assert own['frequency']==given['frequency']
    assert own['prefix']==given['prefix']
    assert given['signs']==[1,1,1]
verification=json.loads((R/'verification.json').read_text())
assert [x for row in rows for x in row['lower_bounds']]==verification['rational_sqrt17_interval']['prefix_lower_bounds']
assert all(q(item['derivative'])==jet(E,item['n']) for item in verification['small_derivatives'])
# Independent recurrence in integer derivative sequences validates jets a second way.
def aj(n):
    if n%2:return F(0)
    return F(4**n-sum(math.comb(n,j)*17**(j//2) for j in range(0,n+1,2))+5*sum(math.comb(n,j)*17**((j-1)//2) for j in range(1,n+1,2)),2)
def bj(n):
    if n%2==0:return F(0)
    return F(sum(math.comb(n,j)*(5**j-17**(j//2)) for j in range(0,n+1,2)),2)
def uj(n):
    if n<0:return F(0)
    return sum(math.comb(n,j)*(bj(j+1)*aj(n-j)-bj(j)*aj(n-j+1)-aj(j)*aj(n-j)) for j in range(n+1))
def vj(n):
    if n<0:return F(0)
    return -4*sum(math.comb(n,j)*bj(j)*aj(n-j) for j in range(n+1))
assert all(jet(E,n)==q(uj(n)+n*vj(n-1)+2*n*(n-1)*uj(n-2)) for n in range(25))
# Exact all-order moment identity: polynomial coefficients in h are the three c arrays.
# Algebra for n=24+h: n(n-1)*2u = 1104u+94hu+2h^2u.
assert 2*24*23==1104 and 2*(24+23)==94
receipt={'status':'PASS','independent_from_candidate_code':True,'A':encode(A),'B':encode(B),'U':encode(U),'V':encode(V),'E':encode(E),'zero_frequency_U':enc(zeroU),'frequency_order_certified':True,'prefix_rows':rows,'jets_0_through_23':jets,'derivative24_literal_identity':True,'mutation_94_instead_of_96_rejected':True,'integer_jet_crosscheck_through':24,'limits':{'address_space_bytes':536870912,'cpu_seconds':35,'threads':1},'credit':0}
(HERE/'exact-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: literal A/B, full U/V table, parity/zero mode, 12 ordered frequencies, 36 strict prefixes, D24 identity, 24 initial jets, independent integer jets, adversarial 94 mutation.')

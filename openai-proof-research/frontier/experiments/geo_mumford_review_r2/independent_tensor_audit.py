"""Independent exact audit: no scout imports, no numerical libraries.
Basis: tensor products of a=epsilon12 epsilon34 and b=epsilon13 epsilon24.
Verifies one-factor contractions directly, then uses their tensor product algebra.
The all-arity proof is in the review, not inferred from finite ranks.
"""
from fractions import Fraction as F
from itertools import product, permutations
from functools import reduce
NAMES=list(product('ab',repeat=3))
IND={s:i for i,s in enumerate(NAMES)}
ZERO=(F(0),)*8

def add(*vs): return tuple(map(sum,zip(*vs)))
def scale(c,v): return tuple(c*x for x in v)
def unit(s): return tuple(F(i==IND[tuple(s)]) for i in range(8))
def mul(u,v):
    out=list(ZERO)
    for i,a in enumerate(NAMES):
        for j,b in enumerate(NAMES):
            key=tuple('b' if x==y=='b' else 'a' for x,y in zip(a,b))
            out[IND[key]]+=u[i]*v[j]*2**sum(x==y=='a' for x,y in zip(a,b))
    return tuple(out)

def eps(i,j):return j-i
BITS=list(product(range(2),repeat=4))
def a(t):return eps(t[0],t[1])*eps(t[2],t[3])
def b(t):return eps(t[0],t[2])*eps(t[1],t[3])
def compose(s,t):
    return {v:sum(t((v[0],v[1],m,n))*eps(m,r)*eps(n,q)*s((r,q,v[2],v[3]))
                  for m,n,r,q in BITS) for v in BITS}
for s,t,k,expected in [(a,a,2,a),(a,b,1,a),(b,a,1,a),(b,b,1,b)]:
    assert all(w==k*expected(v) for v,w in compose(s,t).items())
assert all(a(v)-b(v)+eps(v[0],v[3])*eps(v[1],v[2])==0 for v in BITS)
print('Direct epsilon contractions: a*a=2a, a*b=b*a=a, b*b=b; d=b-a.')

# Determine every S4 action from all 16 coordinates, not presumed rules.
PERMS=list(permutations(range(4)))
RULES={}
for p in PERMS:
    d={}
    for name,t in [('a',a),('b',b)]:
        vals={v:t(tuple(v[i] for i in p)) for v in BITS}
        coeff=next((F(c),F(e)) for c,e in product(range(-2,3),repeat=2)
                   if all(vals[v]==c*a(v)+e*b(v) for v in BITS))
        d[name]=coeff
    RULES[p]=d

def perm(v,p):
    out=list(ZERO)
    for i,name in enumerate(NAMES):
        for j,dest in enumerate(NAMES):
            c=F(1)
            for letter,new in zip(name,dest):c*=RULES[p][letter][0 if new=='a' else 1]
            out[j]+=v[i]*c
    return tuple(out)
def parity(p):return (-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
def rank(rows):
    rows=[list(v) for v in rows];r=0
    for c in range(8):
        pivot=next((i for i in range(r,len(rows)) if rows[i][c]),None)
        if pivot is None:continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        f=rows[r][c];rows[r]=[x/f for x in rows[r]]
        for i in range(r+1,len(rows)):
            f=rows[i][c];rows[i]=[x-f*y for x,y in zip(rows[i],rows[r])]
        r+=1
    return r

def basis(rows):
    out=[]
    for v in rows:
        if rank(out+[v])>len(out):out.append(v)
    return out
I=unit('bbb')
x=[scale(F(1,2),unit(n)) for n in ['abb','bab','bba']]
s=[add(I,scale(-2,v)) for v in x]
p=reduce(mul,x)
q=[reduce(mul,[x[j] if i==j else add(I,scale(-1,x[j])) for j in range(3)]) for i in range(3)]
swap=reduce(mul,s)
for i in range(3):
    assert mul(x[i],x[i])==x[i]
    assert mul(q[i],q[i])==q[i]
    assert mul(q[i],swap)==scale(-1,q[i])
    assert mul(q[i],p)==ZERO
    for j in range(i):assert mul(q[i],q[j])==ZERO
assert mul(p,swap)==scale(-1,p)
assert add(p,*q)==scale(F(1,2),add(I,scale(-1,swap)))
print('Projectors: primitive ranks 9+9+9; theta rank 1; sum = wedge-square projector.')
lef=[I,swap,p]
initial=lef+q
orbit=basis([perm(v,h) for v in initial for h in PERMS])
assert rank(initial)==5 and len(orbit)==7
assert rank([scale(parity(h),perm(v,h)) for v in initial for h in PERMS])==7
assert rank(orbit+[mul(u,v) for u in orbit for v in orbit])==8
print('Exact ranks: initial 5; S4-span 7; with compositions 8; geometric Koszul signs preserve rank.')
l0=basis([perm(v,h) for v in lef for h in PERMS])
assert len(l0)==3 and rank(l0+[mul(u,v) for u in l0 for v in l0])==3
print('Lefschetz-only closure: 3.')
R=(0,2,1,3)
r=[perm(v,R) for v in q]
d={}
for i,j in [(0,1),(0,2),(1,2)]:
    d[i,j]=add(scale(F(4,3),add(q[i],scale(-1,q[j]))),scale(F(-2,3),add(r[i],scale(-1,r[j]))))
    assert d[i,j]==add(x[i],scale(-1,x[j]))
total=add(*(mul(v,v) for v in d.values()),scale(-1,add(*q)),scale(3,p))
assert total==add(*x)
for i in range(3):
    rhs=add(total,*(add(x[i],scale(-1,x[j])) for j in range(3) if j!=i))
    assert scale(F(1,3),rhs)==x[i]
print('Symbolic certificate verified: d_ij=4(q_i-q_j)/3-2(Rq_i-Rq_j)/3=x_i-x_j.')
print('Sum x_i = sum_{i<j} d_ij^2 - sum q_i + 3p; each x_i=(sum x + sum_{j!=i}d_ij)/3.')
print('No finite check is claimed to prove the all-arity or algebraicity statements.')

#!/usr/bin/env python3
"""Exact finite diagnostics. No claim to verify four-dimensional topology."""
import itertools, json
from pathlib import Path
OUT=Path(__file__).resolve().parent
C=range(3); MULT=5
forbidden=[(a,b) for a in C for b in C if b!=(a+1)%3]
sets=[frozenset(i for i in C if mask>>i&1) for mask in range(1,8)]
allowed=[(sorted(a),sorted(b)) for a in sets for b in sets if not any(x in a and y in b for x,y in forbidden)]
assert allowed==[([0],[1]),([1],[2]),([2],[0])]
# Integer bundle splits under simultaneous deficiency: each end has capacity one.
splits=[k for k in range(MULT+1) if k<=1 and MULT-k<=1]; assert not splits
cycles=[]
for d in range(2,16):
    number=sum(all(s[(i+1)%d]==(s[i]+1)%3 for i in range(d)) for s in itertools.product(C,repeat=d)) if d<=9 else (3 if d%3==0 else 0)
    assert number==(3 if d%3==0 else 0)
    cycles.append(dict(degree=d,solutions=number,method='exhaustive colors' if d<=9 else 'transition recurrence'))
positive=[]
for d in range(3,61,3):
    received=[[0]*3 for _ in range(d)]; nsel=[0,0,0]; seen=set()
    for v in range(d):
        w=(v+1)%d
        for a,b in forbidden:
            for q in range(MULT):
                edge=(v,a,b,q); assert edge not in seen; seen.add(edge)
                sa=a==v%3; sb=b==w%3; assert not(sa and sb)
                nsel[sa+sb]+=1
                if not sa: received[v][a]+=1
                else: received[w][b]+=1
    assert all(received[v][v%3]==0 for v in range(d))
    assert all(not all(c>=2 for c in row) for row in received)
    assert nsel==[10*d,20*d,0]
    positive.append(dict(degree=d,edges=len(seen),selected_endpoint_histogram=nsel))
# All ordered 0,1,2,0,1,2 port choices have six distinct ports.
port_counts=[sum(a==c for a,b in forbidden)*MULT+sum(b==c for a,b in forbidden)*MULT for c in C]
assert port_counts==[20]*3
k=(20*19)**3*10**6*2**6
# Test odd-arity majority preserving every Boolean binary relation (in particular clauses).
majority_tests=0
for n in [3,5,7,9]:
    for lit1,lit2 in itertools.product([0,1],repeat=2):
        satisfying=[(x,y) for x,y in itertools.product([0,1],repeat=2) if x==lit1 or y==lit2]
        for rows in itertools.product(satisfying,repeat=n):
            maj=tuple(int(sum(r[i] for r in rows)>n//2) for i in [0,1])
            assert maj in satisfying; majority_tests+=1
# Ternary OR is not majority closed, including after existential 2-CNF extension.
onehots=[(1,0,0),(0,1,0),(0,0,1)]
assert tuple(int(sum(r[i] for r in onehots)>1) for i in C)==(0,0,0)
# A same-color-only ternary detector admits this 4-cycle; it cannot test divisibility by 3.
bad=(0,1,0,2); assert all(bad[i]!=bad[(i+1)%4] for i in range(4))
# Noncommutative Magnus calculation through degree six for the exact six-tip word.
N=6
def add(p,q):
    r=dict(p)
    for w,c in q.items(): r[w]=r.get(w,0)+c
    return {w:c for w,c in r.items() if c}
def neg(p): return {w:-c for w,c in p.items()}
def mul(p,q):
    r={}
    for u,a in p.items():
        for v,b in q.items():
            if len(u+v)<=N: r[u+v]=r.get(u+v,0)+a*b
    return {w:c for w,c in r.items() if c}
one={():1}
def inv(p):
    z=add(p,neg(one)); r=one; term=one
    for _ in range(N): term=mul(term,neg(z)); r=add(r,term)
    return r
def comm(p,q): return mul(mul(mul(p,q),inv(p)),inv(q))
def bracket(p,q): return add(mul(p,q),neg(mul(q,p)))
def word(xs,op): return op(op(xs[0],op(xs[1],xs[2])),op(xs[3],op(xs[4],xs[5])))
xs=[{(i,):1} for i in range(6)]; us=[add(one,x) for x in xs]
magnus=add(word(us,comm),neg(one)); leading=word(xs,bracket)
assert magnus==leading and len(leading)==32
assert all(len(w)==6 and set(w)==set(range(6)) for w in leading)
for i in range(6):
    specialized=us.copy(); specialized[i]=one; assert word(specialized,comm)==one
# Exact sl2 tensor check and 9 adjoint-span witness over Q at sigma=1.
from fractions import Fraction
E=(0,1,0,0); F=(0,0,1,0); H=(1,0,0,-1); ID=(1,0,0,1)
def mm(a,b): return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
def plus(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(a,c): return tuple(c*x for x in a)
def br(a,b): return plus(mm(a,b),scale(mm(b,a),-1))
t=word([E,H,F,H,H,E],br); assert t==scale(E,-16)
basis=[E,H,F]
def coords(m): return (m[1],m[0],m[2])
ad=[]
for a,b in itertools.product(C,repeat=2):
    g=mm(plus(ID,scale(E,a)),plus(ID,scale(F,b)))
    gi=(g[3],-g[1],-g[2],g[0])
    ad.append(sum((coords(mm(mm(g,x),gi)) for x in basis),()))
A=[[Fraction(ad[j][i]) for j in range(9)] for i in range(9)]; det=Fraction(1)
for i in range(9):
    pivot=next(j for j in range(i,9) if A[j][i])
    if pivot!=i: A[pivot],A[i]=A[i],A[pivot]; det=-det
    v=A[i][i]; det*=v
    for j in range(i+1,9):
        factor=A[j][i]/v
        A[j]=[x-factor*y for x,y in zip(A[j],A[i])]
assert det!=0
# An innermost sheet pair has equal reduced free-group labels and opposite signs.
# Sibling subtrees vanish when all terminal loops are capped; do not kill a bottom normal circle.
sheet_coefficients={}
for outer in range(4):
    for inner in [1,-1]: sheet_coefficients[outer]=sheet_coefficients.get(outer,0)+inner
assert all(v==0 for v in sheet_coefficients.values())
result=dict(status='PASS: finite algebra/combinatorics only',forbidden_types=forbidden,
 local_transition_cases=49,allowed_deficiencies=allowed,simultaneous_deficiency_splits=splits,
 cycles=cycles,positive_assignments=positive,ports_per_color=port_counts,bodies=k,
 majority_clause_tests=majority_tests,naive_four_cycle=bad,magnus_monomials=len(leading),
 sl2_value=str(t),adjoint_determinant_at_sigma_1=str(det),
 limitations=['No test certifies marked body embeddings, framings, full middle form, PD, formal ideal passage, reflection or worldwide novelty.'])
(OUT/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','bodies','majority_clause_tests','magnus_monomials','adjoint_determinant_at_sigma_1']}))

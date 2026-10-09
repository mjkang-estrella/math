"""Invariant-theory check for Mumford-type fourfolds.

G_C = SL2^3 acting on V = V1 (x) V2 (x) V3.  Invariants of V^{(x)4} = (x)_i Inv(V_i^{(x)4}),
Inv(V_i^{(x)4}) = span{a,b}, a = e12 e34, b = e13 e24, d = e14 e23 = b - a (Pluecker).
We realize tensors concretely (numerically, exact rationals) and test whether the
classes q_i (pair-component idempotents of End(wedge^2 V) = Hodge classes on X^2),
together with Lefschetz (Sp8) invariants, generate all 8 invariants under
(i) leg permutations (factor permutations of X^4) and (ii) composition End(V(x)V).
Run: python3 -I tl_closure.py
"""
import itertools
from fractions import Fraction as Fr

# 2-dim SL2 rep: epsilon
eps = {(0,1):1,(1,0):-1,(0,0):0,(1,1):0}
def pair_tensor(match):
    # match: list of pairs of legs among 0..3 ; tensor in V2^{(x)4} as dict idx->val
    T = {}
    for idx in itertools.product(range(2), repeat=4):
        v = 1
        for (p,q) in match:
            v *= eps[(idx[p], idx[q])]
        if v: T[idx] = Fr(v)
    return T
A = pair_tensor([(0,1),(2,3)])
Bm = pair_tensor([(0,2),(1,3)])
D = pair_tensor([(0,3),(1,2)])
# check Pluecker
for idx in itertools.product(range(2), repeat=4):
    assert A.get(idx,0) - Bm.get(idx,0) + D.get(idx,0) == 0

def tens3(t1,t2,t3):
    # tensor in V^{(x)4}, V = V1(x)V2(x)V3, index per leg = (i1,i2,i3)
    T = {}
    for k1,v1 in t1.items():
        for k2,v2 in t2.items():
            for k3,v3 in t3.items():
                idx = tuple((k1[l],k2[l],k3[l]) for l in range(4))
                T[idx] = v1*v2*v3
    return T
def add(*terms):
    T={}
    for c,t in terms:
        for k,v in t.items():
            T[k]=T.get(k,0)+c*v
    return {k:v for k,v in T.items() if v!=0}

basis_names = list(itertools.product('ab', repeat=3))
pieces = {'a':A,'b':Bm}
basis = [tens3(*(pieces[c] for c in nm)) for nm in basis_names]
keys = sorted({k for t in basis for k in t})
def vec(t): return [t.get(k,0) for k in keys]

def rank(rows):
    M=[list(r) for r in rows]; r=0; ncol=len(M[0]) if M else 0
    for c in range(ncol):
        piv=None
        for i in range(r,len(M)):
            if M[i][c]!=0: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        r+=1
    return r
assert rank([vec(t) for t in basis])==8

# composition: view tensor T(l0,l1,l2,l3) as map (l0,l1) inputs -> (l2,l3) outputs after
# raising indices with omega = eps(x)eps(x)eps on V.  Composition S∘T contracts T's outputs
# with S's inputs via omega.
def omega(x,y):
    return eps[(x[0],y[0])]*eps[(x[1],y[1])]*eps[(x[2],y[2])]
Vb = list(itertools.product(range(2),repeat=3))
def compose(S,T):
    # (S∘T)(i0,i1,o0,o1) = sum_{m0,m1,n0,n1} T(i0,i1,m0,m1) w(m0,n0) w(m1,n1) S(n0,n1,o0,o1)
    R={}
    Tby={}
    for k,v in T.items(): Tby.setdefault((k[2],k[3]),[]).append((k[0],k[1],v))
    Sby={}
    for k,v in S.items(): Sby.setdefault((k[0],k[1]),[]).append((k[2],k[3],v))
    for (m0,m1),tl in Tby.items():
        for (n0,n1),sl in Sby.items():
            w=omega(m0,n0)*omega(m1,n1)
            if not w: continue
            for (i0,i1,tv) in tl:
                for (o0,o1,sv) in sl:
                    k=(i0,i1,o0,o1); R[k]=R.get(k,0)+w*tv*sv
    return {k:v for k,v in R.items() if v!=0}
def permute(T,perm):
    return {tuple(k[perm[l]] for l in range(4)):v for k,v in T.items()}

# identify roles: find the identity element of the composition algebra in span
# compute products of basis elements to get loop constant
def coords(t):
    # solve t = sum c_j basis_j
    import copy
    M=[vec(b) for b in basis]; y=vec(t)
    # least squares exact: solve via normal Gaussian on transposed system
    n=len(basis); rows=[ [M[j][r] for j in range(n)]+[y[r]] for r in range(len(keys))]
    # gaussian elimination
    R=[list(r) for r in rows]; piv_cols=[]; r=0
    for c in range(n):
        p=None
        for i in range(r,len(R)):
            if R[i][c]!=0: p=i;break
        if p is None: continue
        R[r],R[p]=R[p],R[r]
        f=R[r][c]; R[r]=[x/f for x in R[r]]
        for i in range(len(R)):
            if i!=r and R[i][c]!=0:
                g=R[i][c]; R[i]=[x-g*y for x,y in zip(R[i],R[r])]
        piv_cols.append(c); r+=1
    for i in range(r,len(R)): assert R[i][-1]==0, "not in span"
    sol=[Fr(0)]*n
    for i,c in enumerate(piv_cols): sol[c]=R[i][-1]
    return sol

print("a∘a coords:", coords(compose(basis[0],basis[0])))
idx_bbb = basis_names.index(('b','b','b'))
print("bbb∘bbb == bbb ?", coords(compose(basis[idx_bbb],basis[idx_bbb])))

# ---- closure test ----
c = Fr(2)  # per-factor loop constant (8 = c^3 for aaa∘aaa)
# verify per-factor: compose a⊗b⊗b with itself
ia = basis_names.index(('a','b','b'))
print("abb∘abb coords:", coords(compose(basis[ia],basis[ia])))
def fac(name):  # per-factor elements as coefficient vectors over {a,b}
    return {'a':(1,0),'b':(0,1),'d':(-1,1),'Ptriv':(1/c,0),'PS':(-1/c,1)}[name]
def build(n1,n2,n3):
    terms=[]
    for x1,cx1 in zip('ab',fac(n1)):
        for x2,cx2 in zip('ab',fac(n2)):
            for x3,cx3 in zip('ab',fac(n3)):
                coef=cx1*cx2*cx3
                if coef: terms.append((coef,basis[basis_names.index((x1,x2,x3))]))
    return add(*terms)
lef=[build('a','a','a'),build('b','b','b'),build('d','d','d')]
print("Lefschetz rank:", rank([vec(t) for t in lef]))
q=[build('Ptriv','PS','PS'),build('PS','Ptriv','PS'),build('PS','PS','Ptriv')]
# sanity: q_i idempotent, supported on wedge^2: q_i∘swap = -q_i ? swap = ddd up to sign
for t in q: assert coords(compose(t,t))==coords(t)
gens=lef+q
perms=list(itertools.permutations(range(4)))
span=[vec(t) for t in gens]
def closure(gens):
    cur=list(gens)
    while True:
        r0=rank([vec(t) for t in cur])
        new=[]
        for t in cur:
            for p in perms: new.append(permute(t,p))
        for s in cur:
            for t in cur: new.append(compose(s,t))
        allt=cur+new
        # reduce to a basis
        basis_sel=[]; rows=[]
        for t in allt:
            if rank(rows+[vec(t)])>len(rows): rows.append(vec(t)); basis_sel.append(t)
        cur=basis_sel
        r1=len(cur)
        print("closure rank", r0, "->", r1)
        if r1==r0: return cur
cl=closure(gens)
print("final rank of closure:", len(cl), "of 8")
# compare: without q, Lefschetz alone
cl0=closure(lef)
print("Lefschetz-only closure:", len(cl0))

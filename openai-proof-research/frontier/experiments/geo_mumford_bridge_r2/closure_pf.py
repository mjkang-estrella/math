"""Closure test for Mumford-type invariants Inv_{SL2^3}(V^{(x)4}), V=V1(x)V2(x)V3.
Independent re-implementation (exact rationals). Basis {a,b}^{(x)3}; per factor
a = e01 e23 (cup-cap), b = e02 e13 (identity after raising), d = e03 e12 = b - a.
Operations: composition in End(V(x)V) (legs 0,1 in, 2,3 out) and S4 leg permutations.
Tests closures of: Lefschetz {aaa,bbb,ddd} together with
  (A) p_i = PS(i) (x) Pt (x) Pt  (projectors onto S_i in Sym^2 V; the Kuga-Satake/RM route)
  (B) P_T = p_1+p_2+p_3           (Galois-symmetric only; no F-twist)
  (C) q_i = Pt(i) (x) PS (x) PS   (projectors onto S_jS_k in wedge^2 V; scout's route)
Run: python3 -I closure_pf.py"""
import itertools
from fractions import Fraction as Fr
eps={(0,1):1,(1,0):-1,(0,0):0,(1,1):0}
def pair(m):
    T={}
    for idx in itertools.product(range(2),repeat=4):
        v=1
        for p,q in m: v*=eps[(idx[p],idx[q])]
        if v: T[idx]=Fr(v)
    return T
A=pair([(0,1),(2,3)]); B=pair([(0,2),(1,3)])
def tens3(t1,t2,t3):
    T={}
    for k1,v1 in t1.items():
        for k2,v2 in t2.items():
            for k3,v3 in t3.items():
                T[tuple((k1[l],k2[l],k3[l]) for l in range(4))]=v1*v2*v3
    return T
names=list(itertools.product('ab',repeat=3)); P={'a':A,'b':B}
basis=[tens3(*(P[c] for c in nm)) for nm in names]
keys=sorted({k for t in basis for k in t})
def vec(t): return [t.get(k,Fr(0)) for k in keys]
def rank(rows):
    M=[list(r) for r in rows]; r=0
    if not M: return 0
    for c in range(len(M[0])):
        piv=next((i for i in range(r,len(M)) if M[i][c]!=0),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        r+=1
    return r
def om(x,y): return eps[(x[0],y[0])]*eps[(x[1],y[1])]*eps[(x[2],y[2])]
def compose(S,T):
    R={}; Tb={}; Sb={}
    for k,v in T.items(): Tb.setdefault((k[2],k[3]),[]).append((k[0],k[1],v))
    for k,v in S.items(): Sb.setdefault((k[0],k[1]),[]).append((k[2],k[3],v))
    for (m0,m1),tl in Tb.items():
        for (n0,n1),sl in Sb.items():
            w=om(m0,n0)*om(m1,n1)
            if not w: continue
            for i0,i1,tv in tl:
                for o0,o1,sv in sl:
                    k=(i0,i1,o0,o1); R[k]=R.get(k,0)+w*tv*sv
    return {k:v for k,v in R.items() if v!=0}
def permute(T,p): return {tuple(k[p[l]] for l in range(4)):v for k,v in T.items()}
def lin(terms):
    T={}
    for c,t in terms:
        for k,v in t.items(): T[k]=T.get(k,0)+c*v
    return {k:v for k,v in T.items() if v!=0}
# loop constant: per factor a∘a = c a  -> determine c numerically
aaa=basis[0]; sq=compose(aaa,aaa)
c3=sq[next(iter(aaa))]/aaa[next(iter(aaa))]; c=round(c3**(Fr(1,3)) if False else 0)
for cc in [Fr(2),Fr(-2)]:
    if cc**3==c3: c=cc
print("loop constant per factor c =",c)
fac={'a':(Fr(1),Fr(0)),'b':(Fr(0),Fr(1)),'d':(Fr(-1),Fr(1)),'Pt':(1/c,Fr(0)),'PS':(-1/c,Fr(1))}
def build(*ns):
    terms=[]
    for xs in itertools.product('ab',repeat=3):
        coef=Fr(1)
        for n,x in zip(ns,xs): coef*=fac[n][0 if x=='a' else 1]
        if coef: terms.append((coef,basis[names.index(xs)]))
    return lin(terms)
lef=[build('a','a','a'),build('b','b','b'),build('d','d','d')]
p=[build('PS','Pt','Pt'),build('Pt','PS','Pt'),build('Pt','Pt','PS')]
q=[build('Pt','PS','PS'),build('PS','Pt','PS'),build('PS','PS','Pt')]
for t in p+q: assert vec(compose(t,t))==vec(t), "not idempotent"
# p_i are mutually orthogonal and sum with others to identity:
ident=build('b','b','b')
allproj=p+q+[build('Pt','Pt','Pt'),build('PS','PS','PS')]
assert vec(lin([(1,t) for t in allproj]))==vec(ident)
perms=list(itertools.permutations(range(4)))
def closure(gens,label):
    cur=[]; rows=[]
    for t in gens:
        if rank(rows+[vec(t)])>len(rows): rows.append(vec(t)); cur.append(t)
    while True:
        r0=len(cur); cand=[permute(t,pp) for t in cur for pp in perms]+[compose(s,t) for s in cur for t in cur]
        for t in cand:
            if rank(rows+[vec(t)])>len(rows): rows.append(vec(t)); cur.append(t)
        print(f"  {label}: {r0} -> {len(cur)}")
        if len(cur)==r0: return len(cur)
print("Lefschetz only:", closure(lef,"L"))
print("Lefschetz + p_1,p_2,p_3 (C-span of F-twisted p_f):", closure(lef+p,"L+p"))
print("Lefschetz + single p_1:", closure(lef+[p[0]],"L+p1"))
print("Lefschetz + P_T=p1+p2+p3 only:", closure(lef+[lin([(1,t) for t in p])],"L+PT"))
print("Lefschetz + q_1,q_2,q_3:", closure(lef+q,"L+q"))

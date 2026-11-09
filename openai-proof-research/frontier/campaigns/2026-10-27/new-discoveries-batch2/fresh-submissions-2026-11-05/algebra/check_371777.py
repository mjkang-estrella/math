"""Exact replay for MathDB 371777 (Arslan-Ahmia-Alemdar arXiv:2512.02404v2, Conjecture 2.6).
Checks, by brute force over G_{c,n} for small c,n:
 (0) statistics reproduce source Table 2 entries;
 (1) symmetry of sum t^{inv~} q^{fmaj};
 (2) closed formula Z = sum_m (tq)^{col(m)} [n;m]_{t^c}[n;m]_{q^c} prod_g A_{m_g}(t^c,q^c);
 (3) proof steps: FS descent-class equidistribution of inv and imaj; Theta bijection;
     maj_u(sigma)=maj(sh_u(y)); imaj(sigma)=maj(sh_nu(x)); shuffle theorem instances.
Exact integer polynomial arithmetic only (dicts of exponent pairs)."""
import itertools, json, sys, hashlib
from collections import Counter
def inv(s): return sum(1 for i in range(len(s)) for j in range(i+1,len(s)) if s[i]>s[j])
def des(s): return frozenset(i+1 for i in range(len(s)-1) if s[i]>s[i+1])
def maj(s): return sum(des(s))
def inverse(s):
    r=[0]*len(s)
    for i,v in enumerate(s): r[v]=i
    return tuple(r)
def imaj(s): return maj(inverse(s))
def std(w):
    r=sorted(w); return tuple(r.index(x) for x in w)
def pmul(A,B):
    C=Counter()
    for (a,b),x in A.items():
        for (c,d),y in B.items(): C[(a+c,b+d)]+=x*y
    return +C
def qmultinom(m,var):  # [n;m]_X as Counter over exponent pairs, var 0 -> first slot
    n=sum(m); num=Counter({(0,0):1})
    # compute via sum over words of inv (MacMahon) is circular; use product formula with exact division in one variable
    def qint_fact(k):
        P=[1]
        for i in range(1,k+1):
            Q=[0]*(len(P)+i-1)
            for a,x in enumerate(P):
                for j in range(i): Q[a+j]+=x
            P=Q
        return P
    def mul1(P,Q):
        R=[0]*(len(P)+len(Q)-1)
        for i,x in enumerate(P):
            for j,y in enumerate(Q): R[i+j]+=x*y
        return R
    def div1(P,Q):
        P=P[:]; R=[0]*(len(P)-len(Q)+1)
        for i in range(len(R)-1,-1,-1):
            R[i]=P[i+len(Q)-1]//Q[-1]
            for j,y in enumerate(Q): P[i+j]-=R[i]*y
        assert all(x==0 for x in P); return R
    den=[1]
    for k in m: den=mul1(den,qint_fact(k))
    P=div1(qint_fact(n),den)
    return Counter({((e,0) if var==0 else (0,e)):x for e,x in enumerate(P) if x})
def A(k,c):  # sum_{w in S_k} T^{imaj} Q^{maj} with T=t^c,Q=q^c
    C=Counter()
    for w in itertools.permutations(range(k)): C[(c*imaj(w),c*maj(w))]+=1
    return C
def scale(C,c): return Counter({(a*c,b*c):x for (a,b),x in C.items()})
def colored_stats(sigma,cols,c):
    n=len(sigma); col=sum(cols)
    key=[((c-t), v) for v,t in zip(sigma,cols)]   # u_i=c-t_i (t=0 -> c): order (3) of the source
    fm=sum(i+1 for i in range(n-1) if key[i]>key[i+1])
    return c*inv(sigma)+col, c*fm+col
def Z_brute(c,n):
    C=Counter()
    for s in itertools.permutations(range(1,n+1)):
        for cols in itertools.product(range(c),repeat=n): C[colored_stats(s,cols,c)]+=1
    return C
def Z_formula(c,n):
    C=Counter()
    for m in itertools.product(range(n+1),repeat=c):
        if sum(m)!=n: continue
        col=sum((c-g)*m[g-1] for g in range(1,c+1))
        term=Counter({(col,col):1})
        term=pmul(term,scale(qmultinom(m,0),c)); term=pmul(term,scale(qmultinom(m,1),c))
        for k in m: term=pmul(term,A(k,c))
        C+=term
    return +C
def maju(u,s): return sum(i+1 for i in range(len(s)-1) if (u[i],s[i])>(u[i+1],s[i+1]))
def shuffle(nu,words):
    it=[iter(w) for w in words]; return tuple(next(it[g]) for g in nu)
out={'table2':None,'cases':[],'fs':[],'theta':[]}
# (0) Table 2 of source (G_{3,2}); entries (perm, colors, fmaj, inv~)
T2=[((2,1),(0,0),3,3),((2,1),(1,0),1,4),((2,1),(2,0),2,5),((2,1),(0,1),4,4),((2,1),(1,1),5,5),((2,1),(2,1),3,6),
    ((2,1),(0,2),5,5),((2,1),(1,2),6,6),((2,1),(2,2),7,7),((1,2),(0,0),0,0),((1,2),(1,0),1,1),((1,2),(2,0),2,2),
    ((1,2),(0,1),4,1),((1,2),(1,1),2,2),((1,2),(2,1),3,3),((1,2),(0,2),5,2),((1,2),(1,2),6,3),((1,2),(2,2),4,4)]
ok=all(colored_stats(p,cl,3)==(iv,fm) for p,cl,fm,iv in T2); out['table2']=ok; assert ok
# (1),(2)
for c,n in [(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(4,2),(4,3),(5,2),(5,3),(2,6)]:
    Zb=Z_brute(c,n); Zf=Z_formula(c,n)
    sym=all(Zb[k]==Zb[(k[1],k[0])] for k in Zb)
    out['cases'].append({'c':c,'n':n,'order':sum(Zb.values()),'symmetric':sym,'formula_equal':Zb==Zf}); print(out['cases'][-1],flush=True)
    assert sym and Zb==Zf
# (3) FS descent classes, n<=6
for n in range(1,7):
    I=Counter(); J=Counter()
    for s in itertools.permutations(range(n)): I[(des(s),inv(s))]+=1; J[(des(s),imaj(s))]+=1
    out['fs'].append({'n':n,'equal':I==J}); assert I==J
# Theta bijection and steps 3-5, for several m
for m in [(2,1),(1,2),(2,2),(1,1,1),(3,2),(2,1,2),(1,3,1),(4,2),(3,3)]:
    n=sum(m); c=len(m); base=[g for g in range(c) for _ in range(m[g])]
    words=sorted(set(itertools.permutations(base))); seen=set(); okstep=True
    shufok=True
    for u in words:
        P=[[i for i in range(n) if u[i]==g] for g in range(c)]
        for s in itertools.permutations(range(n)):
            nu=tuple(u[s.index(v)] for v in range(n))
            om=tuple(std([s[i] for i in P[g]]) for g in range(c))
            seen.add((u,nu,om))
            M=[sum(m[:g]) for g in range(c)]
            y=[tuple(M[g]+om[g][k] for k in range(m[g])) for g in range(c)]
            okstep &= maju(u,s)==maj(shuffle(u,y))
            x=[tuple(P[g][inverse(om[g])[k]] for k in range(m[g])) for g in range(c)]
            okstep &= inverse(s)==shuffle(nu,x) and imaj(s)==maj(shuffle(nu,x))
            okstep &= all(maj(x[g])==imaj(om[g]) for g in range(c))
        # shuffle theorem instance for x of this u with first omega pattern set
    expected=len(words)*len(words)
    for k in m: 
        f=1
        for i in range(2,k+1): f*=i
        expected*=f
    out['theta'].append({'m':m,'bijective':len(seen)==expected==len(words)*sum(1 for _ in itertools.permutations(range(n))),'steps_ok':okstep})
    print(out['theta'][-1],flush=True); assert out['theta'][-1]['bijective'] and okstep
# shuffle theorem instances with arbitrary disjoint letter sets
import random
random.seed(371777); sh=[]
for trial in range(200):
    c=random.randint(2,3); m=[random.randint(1,3) for _ in range(c)]; n=sum(m)
    letters=list(range(n)); random.shuffle(letters)
    ws=[];p=0
    for k in m: ws.append(tuple(letters[p:p+k])); p+=k
    base=[g for g in range(c) for _ in range(m[g])]
    S=Counter()
    for nu in set(itertools.permutations(base)): S[maj(shuffle(nu,ws))]+=1
    e=sum(maj(w) for w in ws); R=qmultinom(m,0)
    ok=S==Counter({a+e:x for (a,b),x in R.items()}); sh.append(ok); assert ok
out['shuffle_theorem_instances']={'count':len(sh),'all_ok':all(sh),'seed':371777}
json.dump(out,open('check_371777-output.json','w'),indent=1,default=list)
print('ALL CHECKS PASSED')

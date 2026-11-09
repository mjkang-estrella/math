import itertools
from collections import Counter
def inv(s): return sum(1 for i in range(len(s)) for j in range(i+1,len(s)) if s[i]>s[j])
def maj(s): return sum(i+1 for i in range(len(s)-1) if s[i]>s[i+1])
def majlex(u,s): return sum(i+1 for i in range(len(s)-1) if (u[i],s[i])>(u[i+1],s[i+1]))
def B(m):
    n=sum(m); base=[g for g,k in enumerate(m) for _ in range(k)]
    words=set(itertools.permutations(base)); D=Counter()
    for s in itertools.permutations(range(n)):
        for u in words: D[(inv(s),majlex(u,s))]+=1
    return D
def M(k):
    D=Counter()
    for s in itertools.permutations(range(k)): D[(inv(s),maj(s))]+=1
    return D
def pmul(A,B):
    C=Counter()
    for (a,b),x in A.items():
        for (c,d),y in B.items(): C[(a+c,b+d)]+=x*y
    return C
def qfact_T(k):
    C=Counter({(0,0):1})
    for i in range(1,k+1): C=pmul(C,Counter({(j,0):1 for j in range(i)}))
    return C
def swap(C): return Counter({(b,a):x for (a,b),x in C.items()})
def pdiv_exact(A,Bd):
    # polynomial division in two variables via lex order; returns quotient or None
    A=Counter({k:v for k,v in A.items() if v}); Q=Counter()
    lead=max(Bd); lc=Bd[lead]
    while A:
        k=max(A); v=A[k]
        if v%lc or k[0]<lead[0] or k[1]<lead[1]: return None
        qk=(k[0]-lead[0],k[1]-lead[1]); qv=v//lc; Q[qk]+=qv
        for kk,vv in Bd.items():
            A[(kk[0]+qk[0],kk[1]+qk[1])]-=vv*qv
        A=Counter({k:v for k,v in A.items() if v})
    return Q
for m in [(2,1),(1,2),(2,2),(3,1),(2,1,1),(3,2),(2,2,1),(4,1),(3,3),(4,2)]:
    n=sum(m)
    num=pmul(qfact_T(n),swap(qfact_T(n)))
    for k in m: num=pmul(num,M(k))
    den=Counter({(0,0):1})
    for k in m: den=pmul(den,pmul(qfact_T(k),swap(qfact_T(k))))
    lhs=pmul(B(m),den)
    print(m, lhs==num, flush=True)

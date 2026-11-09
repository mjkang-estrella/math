# 339402: e(m,n) for K_{m,n}, n<=m<=C(n,2). sg via source eq.(1) (Iršič-Konvalinka arXiv:1806.00302v1):
# min s1+s2, 0<=s1<=n, 0<=s2<=m, C(s1,2)>=m-s2, C(s2,2)>=n-s1 (s1 in the n-part, covering the m-part).
# Real solutions: m = s2 + C(s1,2), n = s1 + C(s2,2) (equivalent to the printed system with i=s1, k=s1+s2).
import sys, json, math, numpy as np
C2=lambda x: x*(x-1)//2
def sg(m,n):
    best=None
    for s1 in range(0,n+1):
        s2=max(0,m-C2(s1))
        r=n-s1
        while C2(s2)<r: s2+=1
        if s2>m: continue
        v=s1+s2
        if best is None or v<best: best=v
    return best
def roots(m,n):
    # b = m - a(a-1)/2 ; b(b-1)/2 + a - n = 0
    P=np.polynomial.polynomial
    b=np.array([m,0.5,-0.5])           # coefficients in a (low->high)
    poly=P.polyadd(P.polymul(b,P.polysub(b,[1]))/2,[-n,1])
    r=P.polyroots(poly)
    out=[]
    for a in r:
        if abs(a.imag)<1e-7:
            a=a.real; out.append(a+m-a*(a-1)/2)
    return out,r
N0,N1=int(sys.argv[1]),int(sys.argv[2])
worst=[]; nreal_none=0
for n in range(N0,N1+1):
    wn=(-1,None)
    for m in range(n,C2(n)+1):
        s=sg(m,n); ks,allr=roots(m,n)
        if not ks:
            nreal_none+=1; e=float('inf')
        else: e=min(abs(s-k) for k in ks)
        ecomplex=min(abs(s-(a+m-a*(a-1)/2)) for a in allr)
        if e>wn[0]: wn=(e,m,s,ks,ecomplex)
    worst.append((n,wn[0],wn[1],wn[2],wn[4]))
    print(json.dumps({'n':n,'max_e_real':wn[0],'at_m':wn[1],'sg':wn[2],'real_k':wn[3],'e_complex_at_that_m':wn[4]}),flush=True)
print('pairs_with_no_real_solution',nreal_none)

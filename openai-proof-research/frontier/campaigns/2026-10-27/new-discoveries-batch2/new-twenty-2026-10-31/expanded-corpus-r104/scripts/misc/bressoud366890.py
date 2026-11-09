# Finite check of Li-Uncu Conjecture 1.6 (MathDB 366890) for small k, i, n. Exact integer polynomial arithmetic.
import sys,itertools,functools,time
import numpy as np
def mul(a,b): return np.convolve(a,b).astype(object) if len(a) and len(b) else np.array([],dtype=object)
@functools.lru_cache(None)
def qbin(a,b,s):  # ordinary q^s-binomial with the source's exception: a<0,b=0 -> 1
    if b==0: return (1,)
    if b<0 or a<0 or b>a: return ()
    num=np.array([1],dtype=object)
    for t in range(b):
        num=mul(num,qpoly(a-t,s))
    den=np.array([1],dtype=object)
    for t in range(1,b+1): den=mul(den,qpoly(t,s))
    q,r=polydiv(num,den); assert not any(r); return tuple(q)
def qpoly(m,s):  # 1 - q^{s m}
    p=[0]*(s*m+1); p[0]=1; p[s*m]-=1; return np.array(p,dtype=object)
def polydiv(n,d):
    n=list(n); out=[0]*(len(n)-len(d)+1)
    for i in range(len(out)):
        c=n[i]//d[0]; out[i]=c
        for j in range(len(d)): n[i+j]-=c*d[j]
    return out,n
def add(acc,p,shift):
    if not len(p): return
    for t,c in enumerate(p):
        if c: acc[t+shift]=acc.get(t+shift,0)+c
def lhs(n,k,i,B):
    acc={}
    for ns in itertools.combinations_with_replacement(range(B,-1,-1),k-1):
        # ns nonincreasing
        e=sum(x*x for x in ns)+sum(ns[i-1:])
        p=np.array(qbin(n-sum(ns[:k-2])-k+i,ns[k-2],2),dtype=object)
        if not len(p): continue
        for j in range(1,k-1):
            a=max(j-i+1,0)
            top=2*n-2*sum(ns[:j-1])-ns[j-1]-ns[j]-2*a
            p=mul(p,np.array(qbin(top,ns[j-1]-ns[j],1),dtype=object))
            if not len(p): break
        add(acc,p,e)
    return {t:c for t,c in acc.items() if c}
def rhs(n,k,i):
    acc={}
    for r in range(-2*n-3,2*n+4):
        sg=1 if r%2==0 else -1
        b=n-k*r+(k-i)*(sg-1)//2
        p=qbin(2*n,b,1) if b>=0 else ()
        if b==0: p=(1,)
        add(acc,[sg*c for c in p],r*(k*r+k-i))
    return {t:c for t,c in acc.items() if c}
t0=time.time(); res=[]
for k in range(5,8):
  for i in range(1,k):
    for n in range(0,9):
      if time.time()-t0>100: break
      B=2*n+2
      L=lhs(n,k,i,B); R=rhs(n,k,i)
      res.append((k,i,n,L==R))
      if L!=R: print('MISMATCH',k,i,n,sorted(L.items())[:8],sorted(R.items())[:8],flush=True)
print('checked',len(res),'all_equal',all(x[3] for x in res),'max per k',{k:max(x[2] for x in res if x[0]==k) for k in set(x[0] for x in res)},flush=True)
print([x[:3] for x in res if not x[3]][:20])

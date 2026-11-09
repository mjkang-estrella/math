"""Spectrum of a Frobenius type-A seaweed p^A(a|b) via the oriented meander (Mayers-Russoniello arXiv:2306.10154, Thm thm:specmeander).
Top edges (from a) oriented right->left, bottom edges (from b) left->right; weight = #forward - #backward.
Entry (i,j) in seaweed iff blockA(i)<=blockA(j) and blockB(i)>=blockB(j). Spectrum = {phi(i)-phi(j): (i,j) allowed, i!=j} + (n-1) zeros."""
from collections import Counter
import sys
def blocks(c):
    out=[];s=0
    for x in c: out.append((s,s+x-1)); s+=x
    return out
def blockid(c):
    r=[]
    for k,x in enumerate(c): r+= [k]*x
    return r
def phi_of(a,b):
    n=sum(a); assert n==sum(b)
    adj=[[] for _ in range(n)]  # (nbr, delta) with phi(nbr)=phi(u)+delta
    E=0
    for (s,e) in blocks(a):
        t=0
        while s+t<e-t:
            u,v=e-t,s+t  # directed u->v : phi(u)=phi(v)+1
            adj[v].append((u,1)); adj[u].append((v,-1)); E+=1; t+=1
    for (s,e) in blocks(b):
        t=0
        while s+t<e-t:
            u,v=s+t,e-t
            adj[v].append((u,1)); adj[u].append((v,-1)); E+=1; t+=1
    if E!=n-1: return None
    phi=[None]*n; phi[n-1]=0; st=[n-1]
    while st:
        u=st.pop()
        for v,d in adj[u]:
            if phi[v] is None: phi[v]=phi[u]+d; st.append(v)
            elif phi[v]!=phi[u]+d: return None
    if any(p is None for p in phi): return None  # not connected => not Frobenius
    return phi
def spectrum(a,b):
    phi=phi_of(a,b)
    if phi is None: return None
    n=sum(a); A=blockid(a); B=blockid(b); C=Counter()
    for i in range(n):
        for j in range(n):
            if i!=j and A[i]<=A[j] and B[i]>=B[j]: C[phi[i]-phi[j]]+=1
    C[0]+=n-1
    return C
def mults(C):
    lo,hi=min(C),max(C); return [C.get(x,0) for x in range(lo,hi+1)],lo,hi
def logconcave(m): return all(m[i]*m[i]>=m[i-1]*m[i+1] for i in range(1,len(m)-1))
def unimodal(m):
    i=0
    while i+1<len(m) and m[i]<=m[i+1]: i+=1
    while i+1<len(m) and m[i]>=m[i+1]: i+=1
    return i==len(m)-1
def fmt(C): return ' '.join(f'{x}^{C[x]}' for x in sorted(C))
if __name__=='__main__':
    for a,b in [((2,4),(1,2,3)),((3,1),(4,)),((3,2,2),(4,2,1)),((8,8,8,1),(25,))]:
        print(a,b,fmt(spectrum(a,b)))

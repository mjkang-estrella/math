from itertools import combinations
from math import comb
from collections import Counter

def odd_set_compositions(n):
    elems=tuple(range(1,n+1)); res=[]
    def rec(remaining, cur):
        if not remaining:
            res.append(tuple(cur)); return
        for r in range(1,len(remaining)+1,2):
            for blk in combinations(remaining, r):
                rest=tuple(x for x in remaining if x not in blk)
                rec(rest, cur+[frozenset(blk)])
    rec(elems,[])
    return res

def odd_compositions(l):
    out=[]
    def rec(rem,cur):
        if rem==0: out.append(tuple(cur)); return
        for p in range(1,rem+1,2): rec(rem-p,cur+[p])
    rec(l,[]); return [c for c in out if all(x%2==1 for x in c)]

def coarsenings(x):
    L=len(x); res=set()
    def gen(idx,cur):
        if idx==L: res.add(tuple(cur)); return
        for j in range(idx+1,L+1):
            if sum(x[idx:j])%2==1: gen(j,cur+[sum(x[idx:j])])
    gen(0,[]); return res

def mu_l(l):
    S=set(odd_compositions(l)); top=tuple([1]*l); memo={}
    def leq(a,b): return a in coarsenings(b)
    def moeb(y,x):
        if y==x: return 1
        if (y,x) in memo: return memo[(y,x)]
        memo[(y,x)] = -sum(moeb(y,z) for z in S if z!=x and leq(z,x) and leq(y,z))
        return memo[(y,x)]
    return sum(moeb(y,top) for y in S)

def cat(m): return comb(2*m,m)//(m+1)
def mu_closed(l):
    if l==1: return 1
    if l%2==1: return 0
    return (-1)**(l//2-1)*cat(l//2-1)

def eulerian(n,k):
    T=[[0]*(n+2) for _ in range(n+1)]; T[0][0]=1
    for m in range(1,n+1):
        for j in range(m):
            T[m][j]=((m-j)*T[m-1][j-1] if j>0 else 0)+(j+1)*T[m-1][j]
    return T[n][k]

def RHS(n): return sum((-1)**k*eulerian(n,k) for k in range(n))

for l in range(1,10):
    assert mu_l(l)==mu_closed(l), l
print("mu values ok:", [mu_l(l) for l in range(1,10)])

print("\nLiteral Conjecture 11.7 check (odd set compositions of [n]):")
for n in range(1,14,2):
    comps=odd_set_compositions(n)
    c=Counter(len(p) for p in comps)
    lhs=sum(2**(n-len(p))*mu_closed(len(p)+1) for p in comps)
    print(n, dict(sorted(c.items())), "LHS=",lhs, "RHS=",RHS(n), "MATCH" if lhs==RHS(n) else "MISMATCH")

print("\nVariant: sum over odd INTEGER compositions with multiplicity n!/prod(parts!)? same thing.")
print("\nVariant with mu_{l(phi)} instead of mu_{l(phi)+1}:")
for n in range(1,14,2):
    comps=odd_set_compositions(n)
    lhs=sum(2**(n-len(p))*mu_closed(len(p)) for p in comps)
    print(n, lhs, RHS(n), "MATCH" if lhs==RHS(n) else "MISMATCH")

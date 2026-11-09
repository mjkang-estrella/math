"""
Literal check of arXiv:2506.12868v1 (Aliniaeifard-Li), Conjecture 11.7 = MathDB 368847.

Conjecture 11.7 (verbatim semantics):
  If n is odd:
     sum_{phi odd set composition of [n]} 2^{n - l(phi)} * mu_{l(phi)+1}
       = sum_{0<=k<=n-1} (-1)^k E(n,k).
  mu_l := sum_{psi <= phi, psi odd set comp} mu(psi, phi) for any odd set comp phi with l(phi)=l;
  depends only on l (Lemma 11.1). Remark 11.2: mu_l = (-1)^{l/2-1} Cat_{l/2-1} for even l,
  mu_1 = 1, mu_l = 0 for odd l > 1.
Order on compositions: psi <= phi iff blocks of psi are unions of CONSECUTIVE blocks of phi
  => psi coarser, 1hat = (1,..,1) is the unique maximum.
E(n,k): Eulerian numbers (permutations of n with k descents).
"""
from itertools import combinations
from math import comb
import sys

# ---------- odd set compositions of [n] ----------
def odd_set_compositions(n):
    elems = tuple(range(1, n+1))
    res = []
    def rec(remaining, cur):
        if not remaining:
            res.append(tuple(cur)); return
        first = remaining[0]
        rest = remaining[1:]
        for r in range(1, len(remaining)+1, 2):
            for extra in combinations(rest, r-1):
                block = frozenset((first,)+extra)
                rec(tuple(x for x in remaining if x not in block), cur+[block])
    rec(elems, [])
    return res

# ---------- odd integer compositions of l, coarsening poset ----------
def odd_compositions(l):
    out=[]
    def rec(rem, cur):
        if rem==0:
            out.append(tuple(cur)); return
        for p in range(1, rem+1, 2):
            if p<=rem: rec(rem-p, cur+[p])
    rec(l, [])
    return [c for c in out if all(x%2==1 for x in c)]

def coarsenings(x):
    """y <= x (y coarser): y obtained by merging consecutive blocks of x, all blocks odd."""
    L=len(x); res=set()
    def gen(idx, cur):
        if idx==L:
            res.add(tuple(cur)); return
        for j in range(idx+1, L+1):
            m = sum(x[idx:j])
            if m%2==1:
                gen(j, cur+[m])
    gen(0,[])
    return res

def mu_l_moebius(l):
    """Brute-force Moebius sum over odd compositions of l below 1hat."""
    S=set(odd_compositions(l))
    top=tuple([1]*l)
    memo={}
    def leq(a,b):  # a <= b (a coarser than b) iff a in coarsenings(b)
        return a in coarsenings(b)
    def moeb(y,x):
        if y==x: return 1
        if (y,x) in memo: return memo[(y,x)]
        s=sum(moeb(y,z) for z in S if z!=x and leq(z,x) and leq(y,z))
        memo[(y,x)]=-s
        return memo[(y,x)]
    return sum(moeb(y, top) for y in S)

def cat(m): return comb(2*m,m)//(m+1)
def mu_l_closed(l):
    if l==1: return 1
    if l%2==1: return 0
    return (-1)**(l//2-1)*cat(l//2-1)

def eulerian(n,k):
    # Eulerian number via recurrence
    A=[[0]*(n+1) for _ in range(n+1)]
    A[0][0]=1
    for m in range(1,n+1):
        for j in range(m):
            A[m][j] = (m-j)*A[m-1][j-1] + (j+1)*A[m-1][j] if j>0 else 1
    return A[n][k]

def RHS(n):
    return sum((-1)**k*eulerian(n,k) for k in range(0,n))

def LHS(n, mu=mu_l_closed):
    tot=0
    for phi in odd_set_compositions(n):
        l=len(phi)
        tot += 2**(n-l)*mu(l+1)
    return tot

if __name__=="__main__":
    print("l : mu_bruteforce vs closed")
    for l in range(1,10):
        print(l, mu_l_moebius(l), mu_l_closed(l))
    print()
    print("n : LHS : RHS  (literal reading)")
    for n in range(1,14,2):
        print(n, LHS(n), RHS(n), "MATCH" if LHS(n)==RHS(n) else "MISMATCH")

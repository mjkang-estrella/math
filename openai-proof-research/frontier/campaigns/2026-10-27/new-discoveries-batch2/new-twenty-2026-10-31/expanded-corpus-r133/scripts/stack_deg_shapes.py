# Direct check: d_n = sum over shape pairs prod 1/h_j via closure of interval down-sets
import sys
from fractions import Fraction
from functools import lru_cache
def shapes(n):
    # binary trees as postorder subtree-size arrays a[j] (size of subtree rooted at postorder position j)
    if n==0: return [()]
    res=[]
    for k in range(n):  # left size k, right n-1-k
        for L in shapes(k):
            for R in shapes(n-1-k):
                res.append(L+R+(n,))
    return res
def weight(a,b):
    n=len(a); m=[0]*n
    for j in range(n):
        lo=min(j-a[j]+1, j-b[j]+1)
        # closure: down-set interval; extend by down-sets of contained nodes
        changed=True
        while changed:
            changed=False
            for k in range(lo,j):
                if m[k]<lo: lo=m[k]; changed=True
        m[j]=lo
    w=Fraction(1)
    for j in range(n): w/= (j-m[j]+1)
    return w
import math
for n in range(1,int(sys.argv[1])+1):
    S=shapes(n); d=sum(weight(a,b) for a in S for b in S)
    print(n, d*math.factorial(n), float(d))

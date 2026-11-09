# MIT. Author: Myeongjin Kang. Exact-formula exploration of (S)_n: D(b) p^2 <= (n+1) P, p=P(W>0), P=E W^+.
from fractions import Fraction as Fr
import random, math
def pP(b):
    """distinct nonzero coefficients assumed (float or Fraction). zeros allowed (dropped)."""
    w=[x for x in b if x!=0]
    p=0; P=0
    for j,bj in enumerate(w):
        if bj>0:
            pr=1
            for l,bl in enumerate(w):
                if l!=j: pr*=bj/(bj-bl)
            p+=pr; P+=bj*pr
    return p,P
def D(b):
    s=sorted(b); m=len(s); return sum((2*i-m+1)*s[i] for i in range(m))
def ratio(b):
    n=len(b); p,P=pP(b)
    if P<=0: return 0.0
    return D(b)*p*p/((n+1)*P)

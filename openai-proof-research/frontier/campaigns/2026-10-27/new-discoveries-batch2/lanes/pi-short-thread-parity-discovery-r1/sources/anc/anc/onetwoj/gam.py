# Generic spider-state Grundy values (Prop. 6.1), memoised. Independent small implementation.
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
F,IN,OUT='F','in','out'
def rho(h,d,phi):
    if h==0: return 0
    if phi==F: return h
    if phi==d: return h&1
    return 1 if (h>=2 and h%2==0) else 0
def rhoF(h,phi):
    if h==0: return 0
    return h&1 if phi==F else h
def step(s,d):
    if s=='N': return 'I' if d==IN else 'O'
    if s=='I': return 'I' if d==IN else 'F'
    if s=='O': return 'O' if d==OUT else 'F'
    return 'F'
def mex(S):
    g=0
    while g in S: g+=1
    return g
@lru_cache(maxsize=None)
def Gam(s,L):
    # L: tuple of legs (h,phi), sorted
    if s=='F':
        v=0
        for h,p in L: v^=rhoF(h,p)
        return v
    if len(L)==0: return 0
    if len(L)==1 and s!='N':
        h,p=L[0]; return rho(h, OUT if s=='I' else IN, p)
    opts=set()
    for idx,(h,p) in enumerate(L):
        rest=L[:idx]+L[idx+1:]
        for j in range(1,h+1):
            for d in (IN,OUT):
                if j==h and p!=F and d!=p: continue
                det=rho(h-j,d,p)
                if j>=2: v=Gam(s,tuple(sorted(rest+((j-1,d),))))
                else: v=Gam(step(s,d),rest)
                opts.add(det^v)
    return mex(opts)
def G(s,*legs): return Gam(s,tuple(sorted(legs)))

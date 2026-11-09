import sys;sys.path.insert(0,'.')
from csc import *
from fractions import Fraction as F
import math,itertools
def rat(v,d=10**6): return F(round(v*d),d)
def poly(N,scales):
    return [(rat(s*math.cos(2*math.pi*i/N)),rat(s*math.sin(2*math.pi*i/N))) for i,s in enumerate(scales)]
# paper 9-gon: a1 at angle of index 0? labels a1,b1,c1,a2,... ccw; b1=(1,0)
X=poly(9,[0.93 if i%3==2 else 1 for i in range(9)])  # rotate so that b1 at index 0 : a1 index -1 = 8 -> i%3==2
r=minimal_obstruction(X);print('paper9 minimal:',r[0], 'center' if not r[0] else '')
for N in [9,11,13,15,17,21]:
    found=[]
    for pat in range(1,2**(N-1)):
        sc=[1]+[0.93 if pat>>j&1 else 1 for j in range(N-1)]
        X=poly(N,sc)
        if csc_center(X) is None:
            ok,w=minimal_obstruction(X)
            if ok: found.append(pat)
        if len(found)>3: break
    print(N,'minimal obstructions with one scale 0.93 (first few patterns):',found[:4])
    if N>=13: break

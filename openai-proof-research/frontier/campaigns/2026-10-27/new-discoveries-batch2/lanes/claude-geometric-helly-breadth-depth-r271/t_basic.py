import sys;sys.path.insert(0,'.')
from csc import *
from fractions import Fraction as F
import itertools,random
# triangle region test vs brute force, and square cross
T=[(0,0),(4,0),(1,3)]
grid=[(F(i,2),F(j,2)) for i in range(-8,13) for j in range(-8,12)]
L,N=data([(F(a),F(b)) for a,b in T])
bad=0
for O in grid:
    a=admissible([(F(a),F(b)) for a,b in T],O,L,N)
    Y=[(F(a),F(b)) for a,b in T];Z=Y+[(2*O[0]-x[0],2*O[1]-x[1]) for x in Y];H=hull(Z)
    b=len(H)>=3 and on_boundary_all(Z,H)
    bad+=(a!=b)
print('triangle grid mismatches',bad,'of',len(grid))
S=[(1,1),(-1,1),(-1,-1),(1,-1)];Sf=[(F(a),F(b)) for a,b in S];L,N=data(Sf)
print('square: (1/2,0)',admissible(Sf,(F(1,2),F(0)),L,N),'(1/2,1/2)',admissible(Sf,(F(1,2),F(1,2)),L,N),'(0,7)',admissible(Sf,(F(0),F(7)),L,N))
random.seed(1);mm=0;cnt=0
for trial in range(300):
    n=random.randint(3,7)
    import math
    ang=sorted(random.random()*6.283 for _ in range(n))
    X=[(F(round(100*math.cos(a)*(1+random.random()*0.3))),F(round(100*math.sin(a)))) for a in ang]
    H=hull(X)
    if len(set(X))<n or not on_boundary_all(X,H): continue
    L,N=data(X)
    g=[(F(i*20),F(j*20)) for i in range(-6,7) for j in range(-6,7)]
    for O in g:
        a=admissible(X,O,L,N);Z=X+[(2*O[0]-x[0],2*O[1]-x[1]) for x in X];H2=hull(Z)
        b=len(H2)>=3 and on_boundary_all(Z,H2);mm+=(a!=b);cnt+=1
print('random polygons: mismatches',mm,'of',cnt)

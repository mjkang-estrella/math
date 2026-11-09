import sys,random,math;sys.path.insert(0,'.')
from topo import *
from csc import admissible,data
from fractions import Fraction as F
random.seed(7)
# 1) pieces description vs exact criterion
bad=0
for t in range(100):
    T=[(F(random.randint(-20,20)),F(random.randint(-20,20))) for _ in range(3)]
    if cr(sub(T[1],T[0]),sub(T[2],T[0]))==0: continue
    L,N=data(T)
    for s in range(60):
        p=(F(random.randint(-60,60),2),F(random.randint(-60,60),2))
        bad+= inM(T,p)!=admissible(T,p,L,N)
print('piece-description mismatches',bad)
# 2) topology of pairwise intersections for triangles from convex configurations
from csc import hull
stats={}
for t in range(int(sys.argv[1])):
    n=random.randint(4,6)
    ang=sorted(random.uniform(0,2*math.pi) for _ in range(n))
    X=[(F(round(100*math.cos(a)*random.uniform(.6,1.4))),F(round(100*math.sin(a)*random.uniform(.6,1.4)))) for a in ang]
    if len(hull(X))!=n: continue
    trip=list(combinations(X,3));T1,T2=random.sample(trip,2)
    r=topology([T1,T2]);stats[r]=stats.get(r,0)+1
    if r not in [(1,1)]: print('nontrivial',r,T1,T2)
print(stats)

import sys,random,math;sys.path.insert(0,'.')
from topo import pieces,feasible
from csc2 import center
from csc import hull
from itertools import combinations
from fractions import Fraction as F
random.seed(11)
def rnd(v):return F(round(v*10**4),10**4)
while True:
    n=6;ang=sorted(random.uniform(0,2*math.pi) for _ in range(n))
    X=[(rnd((1+random.uniform(-.08,.08))*math.cos(a)),rnd((1+random.uniform(-.08,.08))*math.sin(a))) for a in ang]
    if len(hull(X))==6 and center(X) is None and all(center(X,skip=i) is not None for i in range(6)): break
print('6-point minimal obstruction',X)
tr=list(combinations(X,3));emp=0
def inter(Ts):
    cells=[[]]
    for Tr in Ts:
        cells=[q+H for q in cells for H in pieces(Tr) if feasible(q+H)]
        if not cells: return 0
    return len(cells)
allc=inter(tr);print('cells of full intersection of all 20 M_T:',allc)
for s in combinations(range(20),3):
    if inter([tr[i] for i in s])==0: emp+=1
print('empty triples',emp)

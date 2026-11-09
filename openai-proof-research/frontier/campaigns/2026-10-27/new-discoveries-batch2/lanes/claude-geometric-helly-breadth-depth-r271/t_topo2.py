import sys,random,math,time;sys.path.insert(0,'.')
from topo import *
from csc import hull
from fractions import Fraction as F
random.seed(int(sys.argv[1]));T=float(sys.argv[2]);t0=time.time()
stats={};worst=(0,None)
def comps(Ts):
    # components and euler char via incremental cell products with pruning
    cells=[[]]
    for Tr in Ts:
        cells=[q+H for q in cells for H in pieces(Tr) if feasible(q+H)]
        if not cells: return (0,0)
    return topology_cells(cells)
def topology_cells(cells):
    n=len(cells);par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]];x=par[x]
        return x
    E=set()
    for i,j in combinations(range(n),2):
        if feasible(cells[i]+cells[j]): E.add((i,j));par[f(i)]=f(j)
    c=len(set(f(i) for i in range(n)))
    chi=n-len(E);level=sorted(E);k=2
    while level:
        nxt=set()
        for s in level:
            for j in range(s[-1]+1,n):
                if all((i,j) in E for i in s) and feasible(sum((cells[i] for i in s),[])+cells[j]): nxt.add(s+(j,))
        level=sorted(nxt);chi+=(-1)**k*len(level);k+=1
    return (c,chi)
while time.time()-t0<T:
    n=random.randint(5,8)
    ang=sorted(random.uniform(0,2*math.pi) for _ in range(n))
    X=[(F(round(100*math.cos(a)*random.uniform(.7,1.3))),F(round(100*math.sin(a)*random.uniform(.7,1.3)))) for a in ang]
    if len(hull(X))!=n: continue
    trip=list(combinations(X,3));s=random.randint(2,5)
    Ts=random.sample(trip,s)
    r=comps(Ts);stats[(s,)+r]=stats.get((s,)+r,0)+1
    if r[0]>worst[0]: worst=(r[0],Ts)
    if r[0]!=r[1]: print('HOLE?',r,Ts);sys.stdout.flush()
print(sorted(stats.items()));print('worst comps',worst[0])

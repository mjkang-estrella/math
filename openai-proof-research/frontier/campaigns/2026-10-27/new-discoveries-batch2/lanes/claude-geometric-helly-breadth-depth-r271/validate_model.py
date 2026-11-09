import sys,random,math;sys.path.insert(0,'.')
from model import *
from csc import csc_center,minimal_obstruction
from fractions import Fraction as F
random.seed(5)
# Q: centrally symmetric 2m-gon with vertices q_1..q_m, -q_1..-q_m ccw; d_j = q_{j+1}-q_j (edge e_j), j=0..m with q_0 := -q_m
agree=dis=0;stats={}
for trial in range(400):
    m=random.choice([3,3,4])
    ang=sorted(random.uniform(0,math.pi) for _ in range(m))
    q=[(F(round(100*math.cos(a))),F(round(100*math.sin(a)))) for a in ang]
    full=q+[(-x,-y) for x,y in q]
    from csc import hull
    if len(hull(full))!=2*m: continue
    eps=F(1,10**4)
    u=[(F(random.randint(-9,9)),F(random.randint(-9,9))) for _ in range(2*m)]
    X=[(full[i][0]+eps*u[i][0],full[i][1]+eps*u[i][1]) for i in range(2*m)]
    if len(hull(X))!=2*m: continue
    ws=[((u[j][0]+u[j+m][0])/2,(u[j][1]+u[j+m][1])/2) for j in range(m)]
    qq=[(-q[-1][0],-q[-1][1])]+q   # q_0=-q_m
    # pair j uses double cone spanned by d_{j-1}=q_j-q_{j-1} and d_j=q_{j+1}-q_j (indices into full polygon)
    ds=[]
    ext=[(-q[-1][0],-q[-1][1])]+q+[(-q[0][0],-q[0][1])]
    ds=[(ext[i+1][0]-ext[i][0],ext[i+1][1]-ext[i][1]) for i in range(m+1)]
    fm=feasible(ws,ds,range(m)) is not None
    fe=csc_center(X) is not None
    stats[(m,fm,fe)]=stats.get((m,fm,fe),0)+1
print(stats)

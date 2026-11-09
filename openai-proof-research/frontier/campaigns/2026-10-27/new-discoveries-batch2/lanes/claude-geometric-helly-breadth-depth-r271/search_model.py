import sys,random,math;sys.path.insert(0,'.')
from model import *
from fractions import Fraction as F
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def dirs(m):
    ang=sorted(random.uniform(0,math.pi) for _ in range(m-1))
    ang=[0]+ang+[math.pi]
    ds=[]
    for a in ang:
        ds.append((F(round(1000*math.cos(a))),F(round(1000*math.sin(a)))))
    ds[-1]=(-ds[0][0],-ds[0][1])
    return ds
best={}
import time;t0=time.time()
while time.time()-t0<float(sys.argv[2]) if len(sys.argv)>2 else 60:
    m=random.randint(3,9)
    ds=dirs(m);ws=[(F(random.randint(-20,20)),F(random.randint(-20,20))) for _ in range(m)]
    if feasible(ws,ds,range(m)) is not None: continue
    # greedy reduce to a minimal infeasible subsystem; record its size
    idx=list(range(m))
    changed=True
    while changed:
        changed=False
        for j in list(idx):
            r=[i for i in idx if i!=j]
            if feasible(ws,ds,r) is None: idx=r;changed=True;break
    k=len(idx);best[k]=best.get(k,0)+1
    if k==m and m>=4: print('FULL minimal m=',m,ws,ds);sys.stdout.flush()
print(best)

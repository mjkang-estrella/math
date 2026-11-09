import sys,random,math,time;sys.path.insert(0,'.')
from topo import pieces,feasible
from csc2 import center
from csc import hull,on_boundary_all
from itertools import combinations
from fractions import Fraction as F
random.seed(int(sys.argv[1]));T=float(sys.argv[2]);t0=time.time()
def empty3(Ts):
    cells=[[]]
    for Tr in Ts:
        cells=[q+H for q in cells for H in pieces(Tr) if feasible(q+H)]
        if not cells: return True
    return False
def rnd(v):return F(round(v*10**6),10**6)
st={'obst':0,'three':0,'fail':0}
while time.time()-t0<T:
    if random.random()<0.5:
        N=random.choice([9,11,13]);dl=(1-math.cos(math.pi/N))/2;t=[random.uniform(-1,5) for _ in range(N)]
        X=[(rnd((1-dl*t[k])*math.cos(2*math.pi*k/N)),rnd((1-dl*t[k])*math.sin(2*math.pi*k/N))) for k in range(N)]
    else:
        n=random.randint(6,10);ang=sorted(random.uniform(0,2*math.pi) for _ in range(n));e=random.choice([.03,.08])
        X=[(rnd((1+random.uniform(-e,e))*math.cos(a)),rnd((1+random.uniform(-e,e))*math.sin(a))) for a in ang]
    H=hull(X)
    if len(H)!=len(X): continue
    if center(X) is not None: continue
    st['obst']+=1
    # reduce to a minimal obstruction first (cheaper triangle families)
    Y=list(X);changed=True
    while changed:
        changed=False
        for i in range(len(Y)):
            if center(Y,skip=i) is None: Y=Y[:i]+Y[i+1:];changed=True;break
    tr=list(combinations(Y,3))
    ok=False
    for a in range(len(tr)):
        for b in range(a+1,len(tr)):
            for c in range(b+1,len(tr)):
                if empty3([tr[a],tr[b],tr[c]]): ok=True;break
            if ok:break
        if ok:break
    st["three" if ok else "fail"]+=1;print(st,len(Y));sys.stdout.flush()
    if not ok: print('NO 3-TRIANGLE WITNESS, minimal size',len(Y),Y);sys.stdout.flush()
print(st)

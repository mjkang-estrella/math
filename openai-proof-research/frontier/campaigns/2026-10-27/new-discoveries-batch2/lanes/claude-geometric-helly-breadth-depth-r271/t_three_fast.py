import sys,random,math,time;sys.path.insert(0,'.')
from topo import pieces,feasible
from csc2 import center
from csc import hull
from itertools import combinations
from fractions import Fraction as F
random.seed(int(sys.argv[1]));T=float(sys.argv[2]);t0=time.time()
def fl(H): return [(float(a),float(b),float(c)) for a,b,c in H]
def ffeas(H,eps=1e-9):
    for i in range(len(H)):
        a1,b1,c1=H[i]
        for j in range(i+1,len(H)):
            a2,b2,c2=H[j];d=a1*b2-a2*b1
            if abs(d)<1e-15: continue
            x=(c1*b2-c2*b1)/d;y=(a1*c2-a2*c1)/d
            if all(a*x+b*y<=c+eps*(1+abs(c)) for a,b,c in H): return True
    return False
def empty_exact(Ts):
    cells=[[]]
    for Tr in Ts:
        cells=[q+H for q in cells for H in pieces(Tr) if feasible(q+H)]
        if not cells: return True
    return False
def rnd(v):return F(round(v*10**6),10**6)
st={'min_obst':0,'witnessed':0,'none':0};sizes={}
while time.time()-t0<T:
    if random.random()<0.6:
        N=random.choice([9,11,13]);dl=(1-math.cos(math.pi/N))/2;t=[random.uniform(-1,5) for _ in range(N)]
        X=[(rnd((1-dl*t[k])*math.cos(2*math.pi*k/N)),rnd((1-dl*t[k])*math.sin(2*math.pi*k/N))) for k in range(N)]
    else:
        n=random.randint(7,10);ang=sorted(random.uniform(0,2*math.pi) for _ in range(n));e=random.choice([.03,.08])
        X=[(rnd((1+random.uniform(-e,e))*math.cos(a)),rnd((1+random.uniform(-e,e))*math.sin(a))) for a in ang]
    if len(hull(X))!=len(X) or center(X) is not None: continue
    Y=list(X);changed=True
    while changed:
        changed=False
        for i in range(len(Y)):
            if center(Y,skip=i) is None: Y=Y[:i]+Y[i+1:];changed=True;break
    if len(hull(Y))!=len(Y): continue
    st['min_obst']+=1;sizes[len(Y)]=sizes.get(len(Y),0)+1
    tr=list(combinations(Y,3));P=[[fl(H) for H in pieces(t)] for t in tr]
    # pair cells (float)
    found=None
    for a in range(len(tr)):
        for b in range(a+1,len(tr)):
            pc=[h1+h2 for h1 in P[a] for h2 in P[b] if ffeas(h1+h2)]
            for c in range(b+1,len(tr)):
                if not any(ffeas(q+h3) for q in pc for h3 in P[c]):
                    if empty_exact([tr[a],tr[b],tr[c]]): found=(a,b,c);break
            if found:break
        if found:break
    if found: st['witnessed']+=1
    else: st['none']+=1;print('NO WITNESS',Y,flush=True)
    print(st,sizes,flush=True)

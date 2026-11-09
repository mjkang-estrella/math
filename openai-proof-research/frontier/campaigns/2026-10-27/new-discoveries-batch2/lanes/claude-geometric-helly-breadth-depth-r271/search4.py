import sys,random,math,time;sys.path.insert(0,'.')
from model import *
from fractions import Fraction as F
random.seed(int(sys.argv[1]));T=float(sys.argv[2]);m=int(sys.argv[3])
t0=time.time();n=0;hits=0;inf=0
def rd(a): return (F(round(10**4*math.cos(a))),F(round(10**4*math.sin(a))))
while time.time()-t0<T:
    n+=1
    # arcs: interior-disjoint, possibly with gaps: choose 2m sorted angles, arcs [a1,a2],[a3,a4],... or partition
    if random.random()<0.5:
        ang=[0]+sorted(random.uniform(0,math.pi) for _ in range(m-1))+[math.pi]
        ds=[rd(a) for a in ang];ds[-1]=(-ds[0][0],-ds[0][1])
        pairs=[(ds[j],ds[j+1]) for j in range(m)]
    else:
        ang=sorted(random.uniform(0,math.pi) for _ in range(2*m))
        pairs=[(rd(ang[2*j]),rd(ang[2*j+1])) for j in range(m)]
    sc=random.choice([1,3,10,30])
    ws=[(F(round(random.gauss(0,sc)*100),100),F(round(random.gauss(0,sc)*100),100)) for _ in range(m)]
    # flatten to model format: per-constraint (w,d1,d2)
    def feas(idx):
        from itertools import combinations
        L=[]
        for j in idx: L+=[(ws[j],pairs[j][0]),(ws[j],pairs[j][1])]
        c=set(ws[j] for j in idx)
        for a,b in combinations(L,2):
            P=meet(a,b)
            if P is not None:c.add(P)
        for O in c:
            if all(inD(O,ws[j],*pairs[j]) for j in idx):return True
        return False
    if feas(range(m)): continue
    inf+=1
    from itertools import combinations
    if all(feas(list(s)) for s in combinations(range(m),m-1)):
        hits+=1;print('HIT',ws,pairs);sys.stdout.flush()
        if hits>2:break
print('trials',n,'infeasible',inf,'minimal-size-m',hits)

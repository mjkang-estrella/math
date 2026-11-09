import sys,random,math,time;sys.path.insert(0,'.')
from csc2 import center,is_min_obstruction
from fractions import Fraction as F
seed,T=int(sys.argv[1]),float(sys.argv[2]);regime=sys.argv[3]
random.seed(seed);t0=time.time();sizes={};best=None
def rnd(v):return F(round(v*10**9),10**9)
while time.time()-t0<T:
    n=random.randint(9,17)
    if regime=='odd':
        N=random.choice([9,11,13,15,17]);n=N;dl=(1-math.cos(math.pi/N))/2
        t=[random.uniform(-1,random.choice([3,5,8])) for _ in range(N)]
        X=[(rnd((1-dl*t[k])*math.cos(2*math.pi*k/N)),rnd((1-dl*t[k])*math.sin(2*math.pi*k/N))) for k in range(N)]
    else:
        ang=sorted(random.uniform(0,2*math.pi) for _ in range(n));e=random.choice([0.02,0.05,0.1])
        X=[(rnd((1+random.uniform(-e,e))*math.cos(a)*random.choice([1,1])),rnd((1+random.uniform(-e,e))*math.sin(a))) for a in ang]
    if center(X) is not None: continue
    Y=list(X);random.shuffle(Y)
    changed=True
    while changed:
        changed=False
        for i in range(len(Y)):
            if center(Y,skip=i) is None:
                Y=Y[:i]+Y[i+1:];changed=True;break
    k=len(Y);sizes[k]=sizes.get(k,0)+1
    if best is None or k>len(best): best=Y
print(regime,dict(sorted(sizes.items())))
print('largest',len(best))

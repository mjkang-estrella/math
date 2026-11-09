import sys,random,math,time,json;sys.path.insert(0,'.')
from csc2 import center
from csc import hull
from fractions import Fraction as F
seed,T,extra=int(sys.argv[1]),float(sys.argv[2]),int(sys.argv[3]);random.seed(seed);t0=time.time()
def q(v):return F(round(v*10**5),10**5)
N=9;dl=(1-math.cos(math.pi/N))/2;base=[1,1,3,0,0,3,0,0,3]
def score(X):
    if len(hull(X))!=len(X) or center(X) is not None: return -1
    return sum(center(X,skip=i) is not None for i in range(len(X)))
best=(-2,None)
while time.time()-t0<T:
    ang=[2*math.pi*k/N for k in range(N)];rad=[1-dl*b for b in base]
    for e in range(extra):
        j=random.randrange(len(ang));a2=ang[(j+1)%len(ang)]+(2*math.pi if j==len(ang)-1 else 0)
        ang.insert(j+1,(ang[j]+a2)/2);rad.insert(j+1,random.uniform(0.97,1.0))
    X=[(q(r*math.cos(a)),q(r*math.sin(a))) for r,a in zip(rad,ang)];n=len(X)
    s=score(X)
    if s<0: continue
    for it in range(300):
        if time.time()-t0>T: break
        Y=list(X);i=random.randrange(n);st=dl*random.choice([.05,.2,.6])
        Y[i]=(Y[i][0]+q(random.gauss(0,st)),Y[i][1]+q(random.gauss(0,st)))
        s2=score(Y)
        if s2>=s: X,s=Y,s2
        if s==n: break
    if s>best[0]: best=(s,X);print('best',s,'of',n,flush=True)
    if s==n: print('MINIMAL OBSTRUCTION SIZE',n,json.dumps([[str(a),str(b)] for a,b in X]),flush=True);break

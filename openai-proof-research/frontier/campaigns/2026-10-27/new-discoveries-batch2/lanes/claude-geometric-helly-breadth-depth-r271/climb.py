import sys,random,math,time,json;sys.path.insert(0,'.')
from csc2 import center
from csc import hull
from fractions import Fraction as F
seed,T,n=int(sys.argv[1]),float(sys.argv[2]),int(sys.argv[3]);random.seed(seed);t0=time.time()
def q(v):return F(round(v*10**5),10**5)
def score(X):
    if len(hull(X))!=len(X) or center(X) is not None: return -1
    return sum(center(X,skip=i) is not None for i in range(len(X)))
best=None
while time.time()-t0<T:
    # init near regular odd/ even polygon with radial noise
    dl=(1-math.cos(math.pi/n))/2
    X=[(q((1-dl*random.uniform(-1,5))*math.cos(2*math.pi*k/n+random.uniform(-.2,.2)/n)),q((1-dl*random.uniform(-1,5))*math.sin(2*math.pi*k/n))) for k in range(n)]
    s=score(X)
    if s<0: continue
    it=0
    while time.time()-t0<T and it<400:
        it+=1;Y=list(X);i=random.randrange(n);step=dl*random.choice([.1,.3,1])
        Y[i]=(Y[i][0]+q(random.gauss(0,step)),Y[i][1]+q(random.gauss(0,step)))
        s2=score(Y)
        if s2>=s: X,s=Y,s2
        if s==n: break
    if best is None or s>best[0]: best=(s,X);print('best',s,'of',n,flush=True)
    if s==n:
        print('MINIMAL OBSTRUCTION SIZE',n,json.dumps([[str(a),str(b)] for a,b in X]),flush=True);break

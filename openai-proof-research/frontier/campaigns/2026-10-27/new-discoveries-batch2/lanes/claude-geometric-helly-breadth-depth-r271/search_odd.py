import sys,random,math,time;sys.path.insert(0,'.')
from csc2 import center,is_min_obstruction
from fractions import Fraction as F
seed,T,n=int(sys.argv[1]),float(sys.argv[2]),int(sys.argv[3])
random.seed(seed);t0=time.time()
dl=(1-math.cos(math.pi/n))/2
def X_of(t,tan=None):
    out=[]
    for k in range(n):
        a=2*math.pi*k/n+(tan[k]*dl if tan else 0);r=1-dl*t[k]
        out.append((F(round(r*math.cos(a)*10**9),10**9),F(round(r*math.sin(a)*10**9),10**9)))
    return out
st={'tried':0,'obst':0,'min':0};sizes={}
while time.time()-t0<T:
    mode=random.random()
    if mode<0.5: t=[random.choice([0,0,0,1,2,3,4]) for _ in range(n)]
    else: t=[random.uniform(-1,5) for _ in range(n)]
    X=X_of(t);st['tried']+=1
    if center(X) is not None: continue
    st['obst']+=1
    w=is_min_obstruction(X)
    if w is not None:
        st['min']+=1;print('MIN n=',n,[round(x,3) for x in t]);sys.stdout.flush()
print(n,st)

# Hill-climb over leaf labelings (and random shapes) to maximise E[d_OLA(T,T')]/ht(T) over uniform SPR moves.
import sys,random,json,time
sys.path.insert(0,__file__.rsplit('/',1)[0])
from ola import spr_stats,balanced,height
seed=int(sys.argv[1]); n=int(sys.argv[2]); shape=sys.argv[3]; T=float(sys.argv[4])
rnd=random.Random(seed)
def build(shape_spec,L):
    # shape_spec: nested tuple of sizes -> fill with labels in order
    it=iter(L)
    def f(s):
        if s==1: return next(it)
        return (f(s[0]),f(s[1]))
    return f(shape_spec)
def bal(m):
    return 1 if m==1 else (bal(m//2),bal(m-m//2))
def rshape(m,maxdepth):
    if m==1: return 1
    k=rnd.randint(1,m-1); return (rshape(k,maxdepth),rshape(m-k,maxdepth))
spec=bal(n)
L=list(range(n)); rnd.shuffle(L)
def score(L):
    t=build(spec,L); r=spr_stats(t); return r['mean_moves']/r['height'],r
best,br=score(L); t0=time.time(); it=0
while time.time()-t0<T:
    it+=1
    L2=L[:]; i,j=rnd.sample(range(n),2); L2[i],L2[j]=L2[j],L2[i]
    s,r=score(L2)
    if s>=best: best,br,L=s,r,L2
print(json.dumps({'n':n,'iters':it,'best_ratio':best,'stats':br,'labels':L}))

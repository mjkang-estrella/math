# Exact exhaustive test of Yip's conjecture (MathDB 355956) for given q=p^m, all admissible d.
# Elements of F_q = F_p[X]/(f), f primitive (X generates F_q^*), encoded as base-p integers (digit i = coeff of X^i).
# x in (F_q^*)^d  <=>  log_X(x) ≡ 0 (mod d).  Extension of subfield clique K=F_{p^r}: x notin K with x-s in S for all s in K.
import sys, json, resource, time, array
cpu=int(sys.argv[2]) if len(sys.argv)>2 else 600
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(cpu,cpu))
sys.path.insert(0,__import__('os').path.dirname(__file__))
from yip_search import polypow, is_irreducible, _prime_factors, divisors
import itertools
def find_primitive(p,m):
    q=p**m
    for tail in itertools.product(range(p),repeat=m):
        f=list(tail)+[1]
        if f[0]==0 or not is_irreducible(f,p): continue
        X=[0,1]+[0]*(m-2) if m>1 else [f[0] and (-f[0])%p]
        if m==1: continue
        one=[1]+[0]*(m-1)
        if all(polypow(X,(q-1)//l,f,p)!=one for l in _prime_factors(q-1)): return f
def run(p,m,only_open=True):
    q=p**m; f=find_primitive(p,m); t0=time.time()
    pw=[p**i for i in range(m+1)]
    # log table by repeated multiplication by X (shift + reduce by monic f)
    log=array.array('l',[-1])*q; cur=[1]+[0]*(m-1)
    for k in range(q-1):
        idx=sum(c*pw[i] for i,c in enumerate(cur)); log[idx]=k
        top=cur[-1]; cur=[0]+cur[:-1]
        if top: cur=[(cur[i]-top*f[i])%p for i in range(m)]
    assert sum(1 for v in log if v<0)==1 and log[0]==-1
    def digits(x): return [(x//pw[i])%p for i in range(m)]
    def sub_idx(x,s):  # index of x - s
        return sum(((x//pw[i]-s//pw[i])%p)*pw[i] for i in range(m))
    res=[]
    for d in range(2,q):
        if (q-1)%(2*d): continue
        rs=[r for r in divisors(m) if r<m and ((q-1)//(p**r-1))%d==0]
        if not rs: continue
        r=max(rs); n=m//r; hyp=p**r>(n-1)**2
        if only_open and hyp: continue
        # subfield elements: log divisible by (q-1)/(p^r-1), plus 0
        step=(q-1)//(p**r-1)
        K=[0]+[x for x in range(1,q) if log[x]%step==0]
        assert len(K)==p**r
        isS=lambda y: y!=0 and log[y]%d==0
        assert all(isS(sub_idx(a,b)) for a in K for b in K if a!=b)
        Kset=set(K); wit=[]; cnt=0
        if r==1:
            for x in range(q):
                if x in Kset: continue
                c=x%p; base=x-c
                if all(log[base+((c-a)%p)]%d==0 and (base+((c-a)%p))!=0 for a in range(p)):
                    cnt+=1
                    if len(wit)<3: wit.append(digits(x))
        else:
            for x in range(q):
                if x in Kset: continue
                if all(isS(sub_idx(x,s)) for s in K):
                    cnt+=1
                    if len(wit)<3: wit.append(digits(x))
        res.append({'q':q,'p':p,'m':m,'d':d,'r':r,'n':n,'thm1_hyp':hyp,'primitive_modulus_low_to_high':f,'extension_count':cnt,'witness_digits_low_to_high':wit,'maximal':cnt==0,'secs':round(time.time()-t0,1)})
        print(json.dumps(res[-1]),flush=True)
    return res
if __name__=='__main__':
    p,m=map(int,sys.argv[1].split(','))
    print(json.dumps({'start':[p,m]}),flush=True); run(p,m)

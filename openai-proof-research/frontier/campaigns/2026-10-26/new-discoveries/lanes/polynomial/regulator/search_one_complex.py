"""Numerical screening only: source-exact one-conjugate-pair product.

See Battistoni 1912.08512v2 eq11 and Battistoni--Molteni2211.16842v3
Sec4. Reduced nodes consist of n-2 real nodes and one radius, placed at c.
The n-2 signed edge ratios are x; g=sin(theta), theta in[-pi/2,pi/2].
No search output is a proof or novelty claim.
"""
import sys, pathlib, math, json, argparse
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'.pydeps'))
import numpy as np
from scipy.optimize import minimize

M=3**7.5/(4*7**3.5)
def conjectured(n):
    return 2**((n+4)//2) if n%2==0 else 2**((n+3)//2)*M

def value_gradient(z,n,c):
    x=z[:-1];theta=z[-1];g=math.sin(theta);dg=math.cos(theta)
    dim=n-1;p=1.;dp=np.zeros(dim)
    for i in range(n-2):
        t=1.;dt=np.zeros(dim)
        for j in range(i+1,n-1):
            h=j-1
            dt=dt*x[h];dt[h]+=t;t*=x[h]
            if i==c or j==c:
                f=1-2*t*g+t*t
                df=2*(t-g)*dt;df[-1]-=2*t*dg
            else:f=1-t;df=-dt
            dp=dp*f+p*df;p*=f
    f=2*dg;df=-2*g
    dp=dp*f;dp[-1]+=p*df;p*=f
    return p,dp

def direct(z,n,c):
    x=z[:-1];g=math.sin(z[-1]);reduced=np.zeros(n-1);reduced[c]=1.
    for i in range(c-1,-1,-1):reduced[i]=x[i]*reduced[i+1]
    for i in range(c,n-2):reduced[i+1]=reduced[i]/x[i]
    nodes=[]
    for i,r in enumerate(reduced):
        if i==c:nodes.extend([complex(g,math.sqrt(1-g*g)),complex(g,-math.sqrt(1-g*g))])
        else:nodes.append(complex(r,0))
    return math.prod(abs(1-nodes[i]/nodes[j]) for i in range(n) for j in range(i+1,n))

def self_check():
    rng=np.random.default_rng(20261026)
    for n in range(3,11):
        for c in range(n-1):
            z=rng.uniform(-.9,.9,n-1)
            p,dp=value_gradient(z,n,c)
            assert abs(p-direct(z,n,c))<1e-9*(1+abs(p))
            for j in range(n-1):
                zz=z.copy();zz[j]+=1e-6;pp=value_gradient(zz,n,c)[0]
                zz[j]-=2e-6;pm=value_gradient(zz,n,c)[0]
                assert abs((pp-pm)/2e-6-dp[j])<1e-5*(1+abs(dp[j]))
    z=np.array([1/math.sqrt(7),-1,1,math.asin(1/(2*math.sqrt(7)))])
    assert abs(value_gradient(z,5,3)[0]-16*M)<1e-10

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--min-n',type=int,default=6)
    ap.add_argument('--max-n',type=int,default=16);ap.add_argument('--starts',type=int,default=30)
    ap.add_argument('--seed',type=int,default=20261026);args=ap.parse_args()
    self_check();rng=np.random.default_rng(args.seed);results=[]
    for n in range(args.min_n,args.max_n+1):
        target=conjectured(n);bounds=[(-1,1)]*(n-2)+[(-math.pi/2,math.pi/2)]
        for c in range((n+0)//2):
            best=(-1.,None)
            for s in range(args.starts):
                # Mix interior, near-boundary, and many clustered-real candidates.
                z=rng.uniform(-1,1,n-1);z[-1]*=math.pi/2
                if s%3==0:z[:-1]=np.sign(z[:-1])*rng.uniform(.75,1,n-2)
                def obj(q):
                    v,d=value_gradient(q,n,c);return -v/target,-d/target
                res=minimize(obj,z,jac=True,method='L-BFGS-B',bounds=bounds,
                    options={'ftol':1e-14,'gtol':1e-9,'maxiter':2000})
                v=value_gradient(res.x,n,c)[0]
                if v>best[0]:best=(v,res.x.tolist())
            row={'n':n,'complex_reduced_index':c,'best':best[0],'target':target,
                 'ratio':best[0]/target,'point':best[1]};results.append(row)
            print(json.dumps(row),flush=True)
            (ROOT/'search-results.json').write_text(json.dumps({'args':vars(args),'results':results},indent=2))
            if best[0]>target*(1+1e-7):print('POTENTIAL_COUNTEREXAMPLE',flush=True);return

if __name__=='__main__':main()

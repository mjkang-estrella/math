"""Actual conjugate-node product; bounded numerical exploration only."""
import pathlib,sys,math,itertools,json,argparse
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'.pydeps'))
import numpy as np
from scipy.optimize import minimize

def evaluate(z,n,complex_positions,signs):
    m=n-len(complex_positions);d=n-1;u=z[:m-1]
    angles=dict(zip(complex_positions,z[m-1:]));ss=dict(zip([i for i in range(m) if i not in angles],signs))
    p=1.;dp=np.zeros(d)
    def multiply(f,df):
        nonlocal p,dp
        dp=dp*f+p*df;p*=f
    for ai,i in enumerate(complex_positions):
        angle=angles[i];df=np.zeros(d);df[m-1+ai]=2*math.cos(angle)
        multiply(2*math.sin(angle),df)
    for i in range(m-1):
        t=1.;dt=np.zeros(d)
        for j in range(i+1,m):
            h=j-1;dt=dt*u[h];dt[h]+=t;t*=u[h]
            if i not in angles and j not in angles:
                s=ss[i]*ss[j];multiply(1-s*t,-s*dt)
            elif i not in angles or j not in angles:
                ci=i if i in angles else j;ri=j if i in angles else i;s=ss[ri]
                a=angles[ci];df=2*(t-s*math.cos(a))*dt
                df[m-1+complex_positions.index(ci)]+=2*t*s*math.sin(a)
                multiply(1-2*t*s*math.cos(a)+t*t,df)
            else:
                for s in [-1,1]:
                    a=angles[i]+s*angles[j];df=2*(t-math.cos(a))*dt
                    df[m-1+complex_positions.index(i)]+=2*t*math.sin(a)
                    df[m-1+complex_positions.index(j)]+=s*2*t*math.sin(a)
                    multiply(1-2*t*math.cos(a)+t*t,df)
    return p,dp

def direct(z,n,cp,signs):
    m=n-len(cp);r=[1.]*m
    for i in range(m-2,-1,-1):r[i]=r[i+1]*z[i]
    angles=dict(zip(cp,z[m-1:]));ss=dict(zip([i for i in range(m) if i not in angles],signs));nodes=[]
    for i in range(m):
        if i in angles:
            a=angles[i];nodes.extend([r[i]*complex(math.cos(a),math.sin(a)),r[i]*complex(math.cos(a),-math.sin(a))])
        else:nodes.append(complex(r[i]*ss[i],0))
    return math.prod(abs(1-nodes[i]/nodes[j]) for i in range(n) for j in range(i+1,n))

def check():
    rng=np.random.default_rng(20261026)
    for n in range(5,10):
        m=n-2;cp=(1,m-1);ss=[(-1)**i for i in range(n-4)]
        z=np.concatenate([rng.uniform(.1,.9,m-1),rng.uniform(.2,3,2)])
        p,dp=evaluate(z,n,cp,ss);assert abs(p-direct(z,n,cp,ss))<1e-9*(1+p)
        for j in range(n-1):
            zz=z.copy();zz[j]+=1e-6;pp=evaluate(zz,n,cp,ss)[0]
            zz[j]-=2e-6;pm=evaluate(zz,n,cp,ss)[0]
            assert abs((pp-pm)/2e-6-dp[j])<1e-5*(1+abs(dp[j]))
    n=6;cp=(2,3);z=np.array([1.,1.,1.,math.pi/3,2*math.pi/3]);assert abs(evaluate(z,n,cp,[1,-1])[0]-216)<1e-9

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=8);ap.add_argument('--starts',type=int,default=15);args=ap.parse_args()
    check();n=args.n;m=n-2;rng=np.random.default_rng(20261026+n)
    targets={5:5**2.5,6:216,7:245.8193,8:7**3.5};target=targets[n];results=[]
    for cp in itertools.combinations(range(m),2):
        for tail in itertools.product([-1,1],repeat=n-5):
            ss=[1,*tail];best=(-1,None)
            for run in range(args.starts):
                z=np.concatenate([rng.uniform(.1,1,m-1),rng.uniform(.01,math.pi-.01,2)])
                if run%2==0:z[:m-1]=rng.uniform(.85,1,m-1)
                def obj(q):
                    v,d=evaluate(q,n,cp,ss);return -v/target,-d/target
                sol=minimize(obj,z,jac=True,bounds=[(0,1)]*(m-1)+[(0,math.pi)]*2,
                    method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-9,'maxiter':2000})
                v=evaluate(sol.x,n,cp,ss)[0]
                if v>best[0]:best=(v,sol.x.tolist())
            row={'n':n,'complex_positions':cp,'real_signs':ss,'best':best[0],'target':target,'point':best[1]};results.append(row)
            if best[0]>max([r['best'] for r in results[:-1]],default=0):print(json.dumps(row),flush=True)
            (ROOT/f'two-complex-n{n}.json').write_text(json.dumps({'args':vars(args),'results':results},indent=2))
            if n!=7 and best[0]>target*(1+1e-7):print('POTENTIAL_COUNTEREXAMPLE',flush=True);return
            if n==7 and best[0]>target+.001:print('POTENTIAL_COUNTEREXAMPLE',flush=True);return
    print('DONE',len(results),max(r['best'] for r in results),flush=True)

if __name__=='__main__':main()

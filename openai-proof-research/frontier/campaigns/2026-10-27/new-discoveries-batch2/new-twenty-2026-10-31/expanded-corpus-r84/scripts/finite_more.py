from pathlib import Path
import json,math,itertools,time,sys
import numpy as np
D=Path(__file__).resolve().parents[1];t=time.time();mode=sys.argv[1];out={'mode':mode,'diagnostic_only':True}
if mode=='stopping':
 def diff(p,n):
  q=1-p;v=np.zeros(n+3);v[:2]=1;U=1.;cat=1
  for k in range(1,n+1):
   if k%2==0:
    j=k//2
    if j>1:cat=cat*(4*j-2)//(j+1)
    U-=cat*p**(j+1)*q**(j-1)
   cont=p*np.r_[v[0],v[:-2]]+q*v[1:]
   if k==n:return U-cont[1]
   v=cont;v[:2]=np.maximum(v[:2],U)
 roots=[]
 for n in range(4,161):
  lo=.46;hi=.5
  for _ in range(42):
   mid=(lo+hi)/2
   if diff(mid,n)>=0:lo=mid
   else:hi=mid
  roots.append([n,lo,hi])
 ev=[x for x in roots if x[0]%2==0];bad=[(x,y) for x,y in zip(ev,ev[1:]) if x[2]>=y[1]]
 out.update(roots=roots,even_monotonicity_unseparated=bad,scope='Bellman recursion for exact source max-minus-walk problem; binary64 bisection 42 iterations, n=4..160; not certified intervals')
elif mode=='weil':
 import sympy
 cases=[]
 for p in list(sympy.primerange(2,129)):
  for n in range(1,8):
   q=p**n
   if q>128:break
   if n==1:poly=[0,1]
   else:
    x=sympy.Symbol('x');poly=None
    for coeff in itertools.product(range(p),repeat=n):
     if not coeff[0]:continue
     if sympy.Poly(x**n+sum(c*x**i for i,c in enumerate(coeff)),x,modulus=p).is_irreducible:poly=list(coeff)+[1];break
   digs=np.array([[(a//p**i)%p for i in range(n)] for a in range(q)])
   add=np.array([[sum(int(c)*p**i for i,c in enumerate((digs[a]+digs[b])%p)) for b in range(q)]for a in range(q)])
   mul=np.zeros((q,q),dtype=int)
   for a in range(q):
    for b in range(q):
     c=np.convolve(digs[a],digs[b]).tolist()
     for k in range(2*n-2,n-1,-1):
      for i in range(n):c[k-n+i]-=c[k]*poly[i]
     mul[a,b]=sum(c[i]%p*p**i for i in range(n))
   powers=np.zeros((q,q),dtype=int);powers[:,0]=1
   for d in range(1,q):powers[:,d]=mul[powers[:,d-1],np.arange(q)]
   powers[0,0]=1
   tr=[]
   for a in range(q):
    z=0
    for i in range(n):z=add[z,powers[a,p**i]]
    assert z<p;tr.append(z)
   tr=np.array(tr);three=[];ds=[d for d in range(1,q-1) if math.gcd(d,q-1)==1]
   if q==2:ds=[1]
   for d in ds:
    sig=set()
    for a in range(1,q):
     # Trace(x^d - ax), constant -1 represented p-1
     vals=tr[add[powers[:,d],mul[p-1,mul[a,np.arange(q)]]]]
     c=np.bincount(vals,minlength=p);sig.add(tuple(int(v-c[-1]) for v in c[:-1]))
    if len(sig)==3:
     nonzero=[s for s in sig if any(s)];symmetric=len(nonzero)==2 and all(x==-y for x,y in zip(*nonzero));three.append({'d':d,'spectrum':sorted(sig),'symmetric':symmetric})
   cases.append({'p':int(p),'n':n,'q':q,'polynomial_low_first':poly,'exponents':len(ds),'three_valued':three})
 out.update(cases=cases,scope='All prime powers q<=128, every unit exponent modulo q-1, every nonzero parameter. Exact cyclotomic coefficient vectors modulo 1+...+z^(p-1).',counterexamples=[c for c in cases if any(not a['symmetric'] for a in c['three_valued'])])
out['wall_seconds']=time.time()-t;(D/'outputs'/f'{mode}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out)[:1500])

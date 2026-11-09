from pathlib import Path
import numpy as np,itertools,sympy,math,json,time,sys
D=Path(__file__).resolve().parents[1];p,n=map(int,sys.argv[1:]);q=p**n;t=time.time();file=D/'outputs'/f'weil-{q}.json';x=sympy.Symbol('x')
for coeff in itertools.product(range(p),repeat=n):
 if coeff[0] and sympy.Poly(x**n+sum(c*x**i for i,c in enumerate(coeff)),x,modulus=p).is_irreducible:poly=list(coeff)+[1];break
v=np.arange(q,dtype=np.int64);digits=[(v//p**i)%p for i in range(n)];add=sum(((digits[i][:,None]+digits[i][None,:])%p)*p**i for i in range(n));cs=[np.zeros((q,q),dtype=np.int64)for _ in range(2*n-1)]
for i in range(n):
 for j in range(n):cs[i+j]=(cs[i+j]+digits[i][:,None]*digits[j][None,:])%p
for k in range(2*n-2,n-1,-1):
 for i in range(n):cs[k-n+i]=(cs[k-n+i]-cs[k]*poly[i])%p
mul=sum(cs[i]*p**i for i in range(n));del cs
powers=np.zeros((q,q),dtype=np.int32);powers[:,0]=1
for d in range(1,q):powers[:,d]=mul[powers[:,d-1],v]
tr=np.zeros(q,dtype=np.int32)
for i in range(n):tr=add[tr,powers[:,p**i]]
assert max(tr)<p
units={d for d in range(1,q-1)if math.gcd(d,q-1)==1};orbits=[]
while units:
 d=min(units);orb={d*pow(p,i,q-1)%(q-1)for i in range(n)}|{pow(d,-1,q-1)*pow(p,i,q-1)%(q-1)for i in range(n)};units-=orb;orbits.append((d,sorted(orb)))
res={'p':p,'n':n,'q':q,'polynomial_low_first':poly,'coverage':'All unit exponents modulo q-1 via Frobenius/inverse equivalence (source Definition5.7); exact cyclotomic coefficient vectors, all nonzero parameters. Each orbit listed.','planned_orbits':len(orbits),'completed_orbits':[],'three_valued':[],'counterexamples':[],'complete':False}
negax=mul[p-1,mul[1:, :]];offset=p*np.arange(q-1)[:,None]
for d,orb in orbits:
 values=tr[add[powers[:,d][None,:],negax]];c=np.bincount((values+offset).ravel(),minlength=(q-1)*p).reshape(q-1,p);sig=np.unique(c[:,:-1]-c[:,-1:],axis=0)
 if len(sig)==3:
  nz=[a.tolist()for a in sig if np.any(a)];symmetric=len(nz)==2 and all(a==-b for a,b in zip(*nz));r={'representative':d,'orbit':orb,'spectrum':sig.tolist(),'symmetric':symmetric};res['three_valued'].append(r)
  if not symmetric:res['counterexamples'].append(r)
 res['completed_orbits'].append({'representative':d,'orbit':orb,'spectrum_size':len(sig)});res['wall_seconds']=time.time()-t
 file.write_text(json.dumps(res,indent=2)+'\n')
res['complete']=True;file.write_text(json.dumps(res,indent=2)+'\n');print('q',q,'orbits',len(orbits),'three-valued',len(res['three_valued']),'counterexamples',len(res['counterexamples']),'wall',time.time()-t)

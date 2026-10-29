import json,math,itertools,random,time
from fractions import Fraction as F
from pathlib import Path
L=Path(__file__).resolve().parent
def exact(a,w):
 s=e=F(0)
 for i,j,k,l in itertools.product(range(len(a)),repeat=4):
  t=w[i]*w[j]*w[k]*w[l];d=a[i]+a[j]+a[k]-2*a[l]
  if d<0:s+=t
  elif d==0:e+=t
 return s,e,s/(1-e)
def dyadic_formula(p,w):
 s=sum(w);n=len(w)
 one=sum(w[k]*(s*s-sum(w[k:])**2) for k in range(n))
 positive=w[0]**3*sum(w[2:])+3*w[0]**2*sum(w[j]*sum(w[j+2:]) for j in range(1,n))
 equalpos=w[0]**3*(w[1] if n>1 else 0)+3*w[0]**2*sum(w[j]*w[j+1] for j in range(1,n-1))
 return p**3*s+3*p*p*s*s+3*p*one+positive,p**4+3*p*sum(t**3 for t in w)+equalpos
out={'finite_checks_are_not_proof':True,'exact':[]}
for n in range(2,9):
 p=F(47,100);w=[(1-p)/n]*n;a=[F(0)]+[1-F(1,2**i) for i in range(1,n+1)]
 s,e,q=exact(a,[p]+w);ss,ee=dyadic_formula(p,w);assert (s,e)==(ss,ee)
 out['exact'].append(dict(N=n,strict=str(s),equality=str(e),renewal_ratio=str(q),decimal=float(q)))
for n in [1,2,3,4,8,16,32,64,128,156,256,512,1024]:
 p=F(474346,1000000);w=[(1-p)/n]*n;s,e=dyadic_formula(p,w)
 out['exact'].append(dict(N=n,formula_only=True,renewal_ratio=str(s/(1-e)),decimal=float(s/(1-e))))
# An explicitly finite experimental search; floating values are not certificates.
rng=random.Random(140);start=time.monotonic();experiments=[]
supports=[]
for n in [6,10,16,24]:supports.append(('dyadic',[F(0)]+[1-F(1,2**i) for i in range(1,n)]))
for n in [6,8,10]:
 for t in range(4):supports.append(('random',sorted(set([0,1000]+[rng.randrange(1,1000) for _ in range(n-2)]))))
for name,a in supports:
 n=len(a);terms=[]
 for ix in itertools.combinations_with_replacement(range(n),4):
  total=sum(a[i] for i in ix);win=sum(3*a[i]>total for i in ix);eq=sum(3*a[i]==total for i in ix)
  if not(win or eq):continue
  den=math.prod(math.factorial(ix.count(i)) for i in set(ix));mult=24//den
  terms.append((ix,mult*win/4,mult*eq/4))
 def fun(w):
  s=e=0.;gs=[0.]*n;ge=[0.]*n
  for ix,c,d in terms:
   v=math.prod(w[i] for i in ix);s+=c*v;e+=d*v
   for i in ix:gs[i]+=c*v/w[i];ge[i]+=d*v/w[i]
  den=1-e
  if den<1e-10:return -1e6,[0.]*n
  return s/den,[(g*den+s*h)/den**2 for g,h in zip(gs,ge)]
 best=None
 for trial in range(3):
  w=[.474346]+[(1-.474346)/(n-1)]*(n-1) if trial==0 else [rng.expovariate(1) for _ in range(n)]
  z=sum(w);w=[x/z for x in w]
  for iteration in range(140):
   v,g=fun(w);step=1.
   for backtrack in range(10):
    ww=[max(1e-14,x*math.exp(step*y)) for x,y in zip(w,g)];z=sum(ww);ww=[x/z for x in ww];vv,_=fun(ww)
    if vv>=v:break
    step/=2
   w=ww
  v,_=fun(w)
  if best is None or v>best[0]:best=(v,w)
 experiments.append(dict(pool=name,n=n,support=[str(x) for x in a],weights=best[1],ratio=best[0],iterations=140,trials=3,global_optimum_claim=False))
 if time.monotonic()-start>90:break
out['floating_search']=experiments;out['floating_wall_seconds']=time.monotonic()-start
out['best_floating']=max(x['ratio'] for x in experiments)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('exact records',len(out['exact']),'floating supports',len(experiments),'best',out['best_floating'])

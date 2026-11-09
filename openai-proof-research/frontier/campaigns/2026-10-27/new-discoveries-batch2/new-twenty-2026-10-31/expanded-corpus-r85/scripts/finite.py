import json,math,itertools,pathlib,sys
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1]
def save(k,o):
 (D/f'outputs/{k}-search.json').write_text(json.dumps(o,indent=2)+'\n');print(k,o,flush=True)
mode=sys.argv[1]
if mode=='primes':
 import numpy as np
 N=10000000;a=np.ones(N+1,dtype=np.bool_);a[:2]=False
 for p in range(2,math.isqrt(N)+1):
  if a[p]:a[p*p::p]=False
 ps=np.flatnonzero(a);M=len(ps)//2;alt=np.cumsum(ps[1:2*M:2]-ps[:2*M:2]);n=np.arange(50,M+1);margin=alt[49:]-ps[49:M]-n*np.log(np.log(n))/5
 save('339371',dict(prime_limit=N,n_range=[50,M],min_lower_margin=float(min(margin)),violations=int(sum(margin<=0)),upper_inequality_tested=False,limitation='floating log diagnostic; lower inequality only; no asymptotic proof'))
 n=np.arange(31,len(ps));diff=np.diff(ps)[30:];p=ps[30:-1]
 save('344009',dict(prime_limit=N,index_range=[31,len(ps)-1],violations=int(sum((diff-1)**2>=p)),criterion='gap>=sqrt(p)+1 iff (gap-1)^2>=p, exact integer arithmetic'))
if mode=='digits':
 vals=[]
 # Every integer with fewer than b digits automatically omits a digit.
 for n in range(1000001):
  b=3;ok=True
  while b**(b-1)<=n:
   q=n;seen=set()
   while q:seen.add(q%b);q//=b
   if len(seen)==b:ok=False;break
   b+=1
  if ok:vals.append(n)
 save('342614',dict(range=[0,1000000],exact_digit_special_integers=vals,count=len(vals),limitation='finite list cannot decide finiteness; standard terminating expansions'))
if mode=='collatz':
 count=0;unresolved=[];longest=(0,None)
 for k in range(-40,42,2):
  for n in range(-100,101):
   count+=1;x=n;seen={};step=0
   while x not in seen and step<10000 and abs(x).bit_length()<10000:
    seen[x]=step;step+=1
    x=(x-k//2+1)//2 if x%2==(k//2-1)%2 else 3*x+3*k-5
   if x not in seen:unresolved.append([k,n,step])
   if step>longest[0]:longest=(step,[k,n])
 save('346005',dict(parameter_even_k=[-40,40],n=[-100,100],orbits=count,step_cap=10000,unresolved=unresolved,longest=longest,limitation='eventual periodicity diagnostic, not literal return to initial n; k=2 includes classical Collatz'))
if mode=='lyapunov':
 out=[]
 for k in range(1,21):
  var=F(0);m4=F(0);rec=[]
  for n in range(1,401):
   weights=[math.comb(n,i) for i in range(n//k+1)];z=sum(weights);mu=sum(F(i*w,z) for i,w in enumerate(weights));v=sum(F(w,z)*(i-mu)**2 for i,w in enumerate(weights));r=sum(F(w,z)*(i-mu)**4 for i,w in enumerate(weights));var+=v;m4+=r
   if n in [50,100,200,400]:rec.append([n,float(m4/var**2) if var else None])
  out.append(dict(k=k,ratios=rec))
 save('340663',dict(b_n='n',A_n='0..floor(n/k)',delta=2,k_range=[1,20],n_range=[1,400],results=out,limitation='exact rational moments; displayed ratios rounded; no limit proof'))
if mode=='multiplicative':
 N=50;primes=[n for n in range(2,N+1) if all(n%d for d in range(2,math.isqrt(n)+1))];best=N;witness=None;hist={}
 for signs in itertools.product([-1,1],repeat=len(primes)):
  f=[1]*(N+1)
  for p,sgn in zip(primes,signs):
   for n in range(p,N+1,p):
    q=n;e=0
    while q%p==0:q//=p;e+=1
    f[n]*=sgn**e
  c=max(itertools.accumulate(f[1:]));hist[c]=hist.get(c,0)+1
  if c<best:best=c;witness=dict(zip(primes,signs))
 save('345755',dict(N=N,prime_assignments=2**len(primes),minimum_one_sided_max=best,witness=witness,histogram=hist,definition='completely multiplicative, matching source',limitation='finite prefixes give no infinite coloring'))
if mode=='mmpp':
 import sympy as s
 rec=[]
 for m,alphabet in [(2,[1,2,3]),(3,[1,2])]:
  count=0;minimum=None;arg=None
  for vals in itertools.product(alphabet,repeat=m*m):
   Q=s.zeros(m);z=0
   for i in range(m):
    for j in range(m):
     if i!=j:Q[i,j]=vals[z];z+=1
    Q[i,i]=-sum(Q[i,j] for j in range(m) if j!=i)
   lam=s.Matrix(vals[z:]);M=Q.T.copy();rhs=s.zeros(m,1)
   for j in range(m):M[m-1,j]=1
   rhs[m-1]=1;pi=M.inv()*rhs;A=s.diag(*lam)-Q;h=A.inv()*s.ones(m,1);v=2*(pi.dot(lam))*(pi.dot(h))-1;count+=1
   if minimum is None or v<minimum:minimum=v;arg=vals
  rec.append(dict(states=m,rate_alphabet=alphabet,instances=count,min_scv=str(minimum),argmin=arg))
 save('342633',dict(results=rec,arithmetic='exact SymPy rationals; complete directed offdiagonal Q rates and positive lambda; no zero-rate edges'))
if mode=='opinions':
 count=0;worst=F(0);bad=[]
 for m,n,levels in [(2,2,3),(2,3,3),(3,3,2)]:
  for ent in itertools.product(range(levels),repeat=m*n):
   a=[F(v,levels-1) for v in ent];xs=[sum(a[i*n:(i+1)*n])/n for i in range(m)];ys=[sum(a[i*n+j] for i in range(m))/m for j in range(n)];count+=1
   thresholds={1-abs(x-y) for x in xs for y in ys};thresholds.add(F(0))
   for delta in thresholds:
    if 0<=delta<F(1,2):
     prob=sum(abs(x-y)>=1-delta for x in xs for y in ys)*F(1,m*n);ex=prob-2*delta*(1-delta);worst=max(worst,ex)
     if ex>0:bad.append([m,n,ent,str(delta),str(ex)])
 save('342179',dict(grids='uniform independent coordinates; conditional event probabilities 0,1/2,1 on 2x2 and 2x3; 0,1 on 3x3',grids_checked=count,all_relevant_delta_thresholds=True,max_excess=str(worst),violations=bad,limitation='does not exhaust arbitrary marginal weights or larger grids'))

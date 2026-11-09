import numpy as np,math,random
rng=random.Random(6502);best=(0,None);x=np.linspace(-1,1,1001)
for trial in range(1200):
 n=rng.randrange(2,9);roots=[]
 while len(roots)+1<n:
  a=rng.uniform(-1,1);b=rng.uniform(0,math.sqrt(1-a*a));roots.extend([a+1j*b,a-1j*b])
 if len(roots)<n:roots.append(rng.uniform(-1,1))
 f=np.poly(roots).real
 for k in range(n):
  rhs=np.max(np.abs(np.polyval(np.polyder(f,k),x)))/math.factorial(n)
  for t in range(n+1,n+13):
   mon=np.zeros(t+1);mon[0]=math.factorial(t-n)/math.factorial(t)
   rem=np.polydiv(mon,f)[1];err=mon.copy();err[-len(rem):]-=rem
   lhs=np.max(np.abs(np.polyval(np.polyder(err,k),x)));ratio=lhs/rhs
   if ratio>best[0]:best=(ratio,{'trial':trial,'n':n,'k':k,'t':t,'roots':[(r.real,r.imag) for r in roots],'f':f.tolist(),'lhs':lhs,'rhs':rhs})
   if ratio>1.000001:print('NUMERIC_CANDIDATE',best,flush=True);raise SystemExit
print('best_monomial_ratio',best,flush=True)

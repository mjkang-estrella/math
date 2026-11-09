# 378162 numerical diagnostic (not a proof). For random monic complex P of degree n and operators
# T in A' (average-preserving Laguerre-Polya type): T1 = (1 - lam D) e^{lam D}, T2 = e^{-a D^2} (a>0),
# test whether Re Z(P) < Re Z(TP) (classical majorization) or Im Z(TP) < Im Z(P) holds.
import numpy as np, json, sys, math
rng=np.random.default_rng(20261101)
def maj(x,y,tol=1e-9):  # x majorized by y (equal sums assumed up to tol)
  x=np.sort(x)[::-1]; y=np.sort(y)[::-1]
  if abs(x.sum()-y.sum())>1e-7*(1+abs(y).sum()): return None
  return bool(np.all(np.cumsum(x)<=np.cumsum(y)+tol))
def apply_T1(c,lam):  # c: coefficients highest first; returns coeffs of (1-lam D) e^{lam D} P
  p=np.poly1d(c); q=np.poly1d([0])
  for k in range(len(c)):  # e^{lam D}P = sum lam^k/k! P^{(k)}
    q=q+np.poly1d(lam**k/math.factorial(k)*p.deriv(k).c) if k>0 else q+p
  r=q-lam*q.deriv(); return r.c
def apply_T2(c,a):
  p=np.poly1d(c); q=np.poly1d([0])
  for k in range(0,len(c)//2+1):
    t=p.deriv(2*k) if k>0 else p
    q=q+np.poly1d(((-a)**k/math.factorial(k))*t.c)
  return q.c
stats={'tested':0,'fail':0,'undefined_sum':0}; worst=[]
for trial in range(int(sys.argv[1])):
  n=int(rng.integers(3,7)); roots=rng.normal(size=n)+1j*rng.normal(size=n)*rng.choice([0.1,1,3])
  c=np.poly(roots)
  for kind in ('T1','T2'):
    par=float(rng.choice([-1,1])*rng.exponential(0.7)) if kind=='T1' else float(rng.exponential(0.7))
    tc=apply_T1(c,par) if kind=='T1' else apply_T2(c,par)
    tr=np.roots(tc); 
    a=maj(roots.real,tr.real); b=maj(tr.imag,roots.imag)
    stats['tested']+=1
    if a is None or b is None: stats['undefined_sum']+=1; continue
    if not a and not b:
      stats['fail']+=1
      if len(worst)<5: worst.append(dict(n=n,kind=kind,par=par,roots=[[z.real,z.imag] for z in roots]))
print(json.dumps(dict(stats=stats,examples=worst)))

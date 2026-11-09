from pathlib import Path
import json,sys,random,math,itertools,time
D=Path(__file__).resolve().parents[1]
def flow():
 import numpy as np
 from scipy.linalg import null_space
 from scipy.optimize import minimize
 E=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
 B=np.zeros((10,15))
 for j,(u,v) in enumerate(E):B[u,j]=-1;B[v,j]=1
 N=null_space(B);rng=np.random.default_rng(110);best=100
 def norms(x):return np.sum((N@x[:-1].reshape(6,2))**2,axis=1)
 def jacnorm(x):
  v=N@x[:-1].reshape(6,2);return (2*N[:,:,None]*v[:,None,:]).reshape(15,12)
 for it in range(100):
  x=np.r_[rng.normal(size=12),4.]
  def con(x):return np.r_[norms(x)-1,x[-1]-norms(x)]
  def jac(x):
   j=jacnorm(x);return np.vstack([np.c_[j,np.zeros(15)],np.c_[-j,np.ones(15)]])
  r=minimize(lambda x:x[-1],x,jac=lambda x:np.r_[np.zeros(12),1],constraints={'type':'ineq','fun':con,'jac':jac},method='SLSQP',options={'maxiter':1000,'ftol':1e-11})
  v=N@r.x[:-1].reshape(6,2);ns=np.sum(v*v,axis=1);ratio=float(max(ns)/min(ns));best=min(best,ratio)
  if ratio<=best+1e-9:(D/'outputs/flow-best.json').write_text(json.dumps({'edges':E,'vectors':v.tolist(),'squared_ratio':ratio,'kirchhoff_max_residual':float(np.max(np.abs(B@v))),'not_a_certificate':True},indent=2))
  print(json.dumps({'iteration':it,'success':bool(r.success),'squared_ratio':ratio,'best':best,'target_squared_ratio':7/3}),flush=True)
def beyond():
 from sympy.combinatorics import Permutation,PermutationGroup
 rng=random.Random(110)
 def group(n,m,k):return PermutationGroup([Permutation(list(range(j-1,-1,-1))+list(range(j,n))) for j in [n,m,k]])
 for n in [104,105,128,129,200,201]:
  pairs=[(n-i,n-j) for i,j in [(1,2),(2,3),(3,5),(5,7),(7,11),(11,17)]]+[(rng.randrange(3,n),2) for _ in range(3)]
  for m,k in pairs:
   G=group(n,m,k);H=group(n+2,m+2,k+2)
   # is_alt_sym is Monte Carlo with one-sided error: positives certify Alt/Sym, negatives inconclusive.
   def sym(g,n):return bool(g.is_alt_sym() and any(p.is_odd for p in g.generators))
   a=sym(G,n);b=sym(H,n+2) if a else None
   print(json.dumps(dict(n=n,m=m,k=k,antecedent_certified_by_sympy=a,consequent_certified_by_sympy=b,consequent_transitive=H.is_transitive() if a else None,method='SymPy Monte Carlo Alt/Sym recognizer; negatives inconclusive')),flush=True)
if __name__=='__main__':globals()[sys.argv[1]]()

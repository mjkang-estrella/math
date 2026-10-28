"""Bounded diagnostic only. Full-rank contraction model for Conjecture 6.6.
No floating result is certified. All output stays beside this script's lane.
"""
import numpy as np
from scipy.optimize import minimize
from pathlib import Path
import json
BASE=Path(__file__).resolve().parents[1]
def invsqrt(G):
 e,v=np.linalg.eigh(G)
 if e[0]<1e-11: raise ValueError('ill conditioned')
 return (v/e**.5)@v.T

def parts(X,p):
 m=len(X);q=m-p
 A=X[:p,:q]; B=X[p:,q:]; C=X[:p,q:]; D=X[p:,:q]
 G=np.block([[np.eye(p),A],[A.T,np.eye(q)]])
 K=np.block([[np.eye(q),B],[B.T,np.eye(p)]])
 H=np.block([[np.zeros((p,q)),C],[D.T,np.zeros((q,p))]])
 Z=invsqrt(G)@H@invsqrt(K)
 lhs=np.sum(A*A)+np.sum(B*B)
 rhs=np.sum(Z[:p,:q]**2)+np.sum(Z[p:,q:]**2)
 return lhs,rhs,min(np.linalg.eigvalsh(G)[0],np.linalg.eigvalsh(K)[0])

def contraction(v,m):
 M=v.reshape(m,m);U,s,V=np.linalg.svd(M,full_matrices=False)
 return (U*np.tanh(s))@V

def loss(v,m,p):
 try:
  lhs,rhs,_=parts(contraction(v,m),p)
  return (lhs-rhs)/max(lhs,1e-30) + 0.0001/lhs
 except ValueError:return 1e3

def main():
 rng=np.random.default_rng(80421);out=[]
 for p,q in [(1,1),(1,2),(2,2),(1,3),(2,3),(3,3)]:
  m=p+q;best=None
  for trial in range(8):
   v=rng.normal(size=m*m)*(0.4 if trial%3==0 else 1.3)
   r=minimize(loss,v,args=(m,p),method='L-BFGS-B',bounds=[(-2.5,2.5)]*(m*m),options={'maxiter':350,'ftol':1e-10})
   X=contraction(r.x,m);lhs,rhs,gap=parts(X,p)
   row={'p':p,'q':q,'trial':trial,'lhs':lhs,'rhs':rhs,'relative_deficit':(lhs-rhs)/max(lhs,1e-30) + 0.0001/lhs,'gram_gap':gap,'max_sv':np.linalg.svd(X,compute_uv=False)[0],'nfev':r.nfev}
   if best is None or row['relative_deficit']<best['relative_deficit']:
    best=row; best['X']=X.tolist();print(json.dumps({k:v for k,v in row.items() if k!='X'}),flush=True)
   if lhs-rhs<-1e-7: break
  out.append(best);(BASE/'projection-search.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()

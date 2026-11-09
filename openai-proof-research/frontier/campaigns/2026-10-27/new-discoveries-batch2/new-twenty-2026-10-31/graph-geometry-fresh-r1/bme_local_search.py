"""Subset certificates suffice for nonedges; infeasibility on a subset proves nothing."""
from bme_search import *

def random_tree(n,rng):
 E=((-1,0),(-1,1),(-1,2))
 for k in range(3,n):
  j=rng.randrange(len(E));u,v=E[j];E=E[:j]+E[j+1:]+(edge(u,1-k),edge(v,1-k),edge(k,1-k))
 return E

def runlocal(n,cap=12):
 rng=random.Random(n+319783);logs=[];start=time.time()
 for trial in range(cap):
  E=random_tree(n,rng);near=tbr(E,n);key0=canon(E,n);choices=[k for k in near if k!=key0];k1=rng.choice(choices);F=near[k1]
  near.update(tbr(F,n));near[key0]=E
  others=[G for k,G in near.items() if k not in (key0,k1)]
  w0=np.array(weights(E,n),dtype=np.int64);w1=np.array(weights(F,n),dtype=np.int64);W=np.array([weights(G,n) for G in others],dtype=np.int64)
  A=np.vstack([np.column_stack([W.T,w1-w0]),np.r_[np.ones(len(W)),0]])
  res=linprog(np.zeros(len(W)+1),A_eq=A,b_eq=np.r_[w1,1],bounds=[(0,None)]*len(W)+[(0,1)],method='highs')
  logs.append({'trial':trial,'columns':len(W),'status':res.status})
  if res.success:
   from fractions import Fraction
   support=np.flatnonzero(res.x[:-1]>1e-8);co=[Fraction(float(res.x[k])).limit_denominator(10**8) for k in support];t=Fraction(float(res.x[-1])).limit_denominator(10**8)
   exact=sum(co)==1 and 0<t<1 and all(sum(c*int(W[k,d]) for c,k in zip(co,support))+t*int(w1[d]-w0[d])==int(w1[d]) for d in range(len(w0)))
   (P/f'bme-local-candidate-{n}.json').write_text(json.dumps({'n':n,'E':E,'F':F,'others':[others[k] for k in support],'coefficients':list(map(str,co)),'t':str(t),'exact_coordinate_check':exact},indent=2));print('CANDIDATE',n,exact,flush=True);break
 (P/f'bme-local-run-{n}.json').write_text(json.dumps({'n':n,'logs':logs,'elapsed':time.time()-start,'meaning':'Only feasible results can supply a full-polytope nonedge witness; no global inference from infeasibility.'},indent=2));print(n,logs,'elapsed',time.time()-start,flush=True)
if __name__=='__main__':
 import sys
 runlocal(int(sys.argv[1]),int(sys.argv[2]) if len(sys.argv)>2 else 12)

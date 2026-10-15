"""Exploratory LP only: not a proof unless an exact certificate is emitted."""
import argparse,itertools,json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
p=argparse.ArgumentParser();p.add_argument('--m',type=int,default=6);a=p.parse_args();m=a.m;N=2*m-1

def allowed(w):
 for j in range(len(w)-4):
  if w[j]==w[j+4] and np.prod(w[j:j+4])==-1:return False
 return True
words=[w for w in itertools.product((-1,1),repeat=N) if allowed(w)]
ix={w:i for i,w in enumerate(words)}
# Symmetries are necessary only for logarithmic Liouville limit laws.
rows={('norm',):0};rhs=[1.]
entries=[]
def row(k):
 if k not in rows:rows[k]=len(rows);rhs.append(0.)
 return rows[k]
for w,i in ix.items():
 entries.append((0,i,1))
 for k,v in [(('st',w[:-1]),1),(('st',w[1:]),-1),(('sym',w),1),(('sym',tuple(-v for v in w)),-1),(('rev',w),1),(('rev',w[::-1]),-1)]:entries.append((row(k),i,v))
 for d in range(1,N):entries.append((row(('pair',d)),i,w[0]*w[d]))
 entries.append((row(('four',)),i,np.prod(w[:4])))
# Equality saturation E X0X1X2X3=1/2.
rhs[rows[('four',)]]=0.5
A=lil_matrix((len(rows),len(words)))
for r,c,v in entries:A[r,c]+=v
B=lil_matrix((2**m,len(words)))
mi={w:i for i,w in enumerate(itertools.product((-1,1),repeat=m))}
for w,i in ix.items():
 B[mi[tuple(-v for v in w[:m])],i]+=0.5
 B[mi[w[::2]],i]-=1
res=linprog(np.zeros(len(words)),A_ub=B.tocsr(),b_ub=np.zeros(2**m),A_eq=A.tocsr(),b_eq=rhs,bounds=(0,None),method='highs')
print(json.dumps(dict(m=m,N=N,states=len(words),equalities=len(rows),status=res.status,message=res.message,nonzero=int(sum(res.x>1e-9)) if res.x is not None else None),indent=2))
if res.x is not None:
 print('max equality error',float(np.max(np.abs(A.tocsr()@res.x-rhs))))
 print('max domination error',float(np.max(B.tocsr()@res.x)))

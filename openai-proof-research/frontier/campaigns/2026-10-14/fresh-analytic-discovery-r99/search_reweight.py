#!/usr/bin/env python3
"""Exploratory eigenvalue search only; no absence or universal verdict."""
import sys,json,itertools,hashlib,tempfile,shutil
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import numpy as np
root=Path(__file__).resolve().parent
base=root/'private/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/verification'
tmp=Path(tempfile.mkdtemp(prefix='r99-search-',dir='/var/tmp'))
receipts={r['path']:r for r in json.loads((root/'source367-receipts.json').read_text())}
for name in ['engine.py']:
 p=base/'independent-certificate'/name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==receipts[str(p.relative_to(root/'private'))]['sha256']
 shutil.copyfile(p,tmp/name)
sys.dont_write_bytecode=True;sys.path.insert(0,str(tmp));import engine as e
e.AEXP=F(3,4);rows,_,_=e.input_tables(base/'checks/original/certificate-inputs.txt');poly=defaultdict(F)
for name,key,n in rows:
 for k,v in e.row_interior(name,key).items():
  if k[0]==0 and k[2]==0:poly[k]+=F(n,e.Q)*v
poly=e.clean(poly)
triples=list(itertools.combinations_with_replacement(range(5),3));dim=6+len(triples)
Ws=np.zeros(dim);Ws[0]=1
Ls=np.zeros((dim,5));Ls[1:6]=np.eye(5)
Xs=np.zeros((dim,5,5,5))
for m,t in enumerate(triples):
 S=np.zeros((5,5,5))
 for p in set(itertools.permutations(t)):S[p]=1
 tr=np.einsum('ijj->i',S)
 for i,j,k in itertools.product(range(5),repeat=3):S[i,j,k]-=(tr[i]*(j==k)+tr[j]*(i==k)+tr[k]*(i==j))/7
 Xs[6+m]=S
assert np.max(abs(np.einsum('mijj->mi',Xs)))<1e-12

def matrix(A,p):
 out=np.zeros((dim,dim));letters='cdefghijklmnopqrstuvwxyz'
 for (h,wp,zp,tr,edges),coef in poly.items():
  scale=float(coef)
  for power in tr:scale*=sum(A**power)
  factors=[];sub=[];slots={5:[],6:[],7:[],8:[]}
  for j,(u,v,power) in enumerate(edges):
   c=letters[j];factors.append(A**power);sub.append(c);slots[u].append(c);slots[v].append(c)
  for c in slots[5]:factors.append(p);sub.append(c)
  count=0
  for _ in range(wp):factors.append(Ws);sub.append('ab'[count]);count+=1
  for c in slots[6]:factors.append(Ls);sub.append('ab'[count]+c);count+=1
  for v in [7,8]:
   if slots[v]:factors.append(Xs);sub.append('ab'[count]+''.join(slots[v]));count+=1
  assert count==2
  out+=scale*np.einsum(','.join(sub)+'->ab',*factors,optimize=True)
 return (out+out.T)/2

rng=np.random.default_rng(9901);A0=[F(1,2),F(1,2),F(-1,2),F(-1,2),F(0)]
for trial in range(60):
 v=[F(int(x)) for x in rng.integers(-5,6,4)];v.append(-sum(v));norm=sum(x*x for x in v)
 if not norm:continue
 dot=sum(x*y for x,y in zip(A0,v));ar=[x-2*dot*y/norm for x,y in zip(A0,v)]
 p=np.zeros(5);p[trial%5]=1
 C=matrix(np.array([float(x) for x in ar]),p);ev,V=np.linalg.eigh(C)
 print(trial,float(ev[0]),flush=True)
 if ev[0]<-1e-5:
  result={'trial':trial,'A':[str(x) for x in ar],'p':[int(x) for x in p],'lowest_eigenvalue':float(ev[0]),'vector':V[:,0].tolist(),'scope':'numerical proposal only; needs exact rational evaluation'}
  (tmp/'proposal.json').write_text(json.dumps(result,indent=2)+'\n');print(tmp/'proposal.json');break
else: print('NO NEGATIVE WITNESS IN BOUNDED SEARCH; no mathematical inference')

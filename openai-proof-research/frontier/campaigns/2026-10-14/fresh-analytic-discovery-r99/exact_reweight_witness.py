#!/usr/bin/env python3
"""Exact rational evaluation of a proposed reweighted-interior counterexample.
Original wrapper MIT. No numerical eigenvalue is used in the sign check.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import itertools,json,sys,tempfile,shutil,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--proposal',type=Path,required=True);args=ap.parse_args()
r=Path(__file__).resolve().parent;b=r/'private/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/verification'
receipts={x['path']:x for x in json.loads((r/'source367-receipts.json').read_text())}
for src in [b/'independent-certificate/engine.py',b/'checks/original/certificate-inputs.txt']:
 assert hashlib.sha256(src.read_bytes()).hexdigest()==receipts[str(src.relative_to(r/'private'))]['sha256']
tmp=Path(tempfile.mkdtemp(prefix='r99-exact-witness-',dir='/var/tmp'));shutil.copyfile(b/'independent-certificate/engine.py',tmp/'engine.py');sys.dont_write_bytecode=True;sys.path.insert(0,str(tmp));import engine as e
v=json.loads(args.proposal.read_text());A=list(map(F,v['A']));p=list(map(F,v['p']));c=[F(round(x*10000),10000) for x in v['vector']];w=c[0];ell=c[1:6];X={ijk:F(0) for ijk in itertools.product(range(5),repeat=3)}
for coeff,t in zip(c[6:],itertools.combinations_with_replacement(range(5),3)):
 S={ijk:F(int(ijk in set(itertools.permutations(t)))) for ijk in X};tr=[sum(S[i,j,j] for j in range(5)) for i in range(5)]
 for i,j,k in X:X[i,j,k]+=coeff*(S[i,j,k]-(tr[i]*(j==k)+tr[j]*(i==k)+tr[k]*(i==j))/7)
assert sum(A)==0 and sum(x*x for x in A)==1 and sum(x*x for x in p)<=1
assert all(sum(X[i,j,j] for j in range(5))==0 for i in range(5))
assert all(X[t]==X[perm] for t in X for perm in itertools.permutations(t))
def value(key):
 h,wp,zp,tr,edges=key
 if h or zp:return F(0)
 pref=w**wp
 for power in tr:pref*=sum(x**power for x in A)
 isolated=[];active=[]
 for edge in edges:
  if edge[0] in (7,8) or edge[1] in (7,8):active.append(edge)
  else:isolated.append(edge)
 for u,v,k in isolated:
  pref*=sum(A[i]**k*(p[i] if u==5 else ell[i])*(p[i] if v==5 else ell[i]) for i in range(5))
 choices=[tuple(i for i in range(5) if not(5 in (u,v)) or p[i]) for u,v,k in active]
 total=F(0)
 for inds in itertools.product(*choices):
  term=F(1);slots={7:[],8:[]}
  for (u,v,k),i in zip(active,inds):
   term*=A[i]**k
   for endpoint in (u,v):
    if endpoint==5:term*=p[i]
    elif endpoint==6:term*=ell[i]
    else:slots[endpoint].append(i)
  for vertex in (7,8):
   if slots[vertex]:term*=X[tuple(slots[vertex])]
  total+=term
 return pref*total
rows,_,_=e.input_tables(b/'checks/original/certificate-inputs.txt');vals={}
for a in [F(29,50),F(3,4)]:
 e.AEXP=a;poly=defaultdict(F)
 for name,key,n in rows:
  for k,coef in e.row_interior(name,key).items():
   if k[0]==0 and k[2]==0:poly[k]+=F(n,e.Q)*coef
 vals[str(a)]=sum(coef*value(key) for key,coef in poly.items())
assert vals['29/50']>0 and vals['3/4']<0,vals
out={'A_diagonal':[str(x) for x in A],'p':[str(x) for x in p],'g':'0','z':'0','w':str(w),'ell':[str(x) for x in ell],'X_symmetric_entries':{','.join(map(str,t)):str(X[t]) for t in itertools.combinations_with_replacement(range(5),3)},'I_exact':{k:str(val) for k,val in vals.items()},'I_decimal_diagnostic':{k:float(val) for k,val in vals.items()},'scope':'Exact algebraic counterexample to fixed-multiplier reweight a=3/4; not Bernoulli solution or full-rigidity counterexample.'}
q=tmp/'witness.json';q.write_text(json.dumps(out,indent=2)+'\n');print(q);print(hashlib.sha256(q.read_bytes()).hexdigest());print(out['I_decimal_diagnostic'])

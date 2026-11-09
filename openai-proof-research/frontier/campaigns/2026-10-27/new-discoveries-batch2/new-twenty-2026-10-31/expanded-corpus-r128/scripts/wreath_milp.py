import pathlib,sys,random,itertools,json
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import csc_matrix
D=pathlib.Path(__file__).resolve().parents[1];k=5;n=11;rng=random.Random(128)
def dyck(a=0,b=0,w=()):
 if b==k:yield w;return
 if a<k:yield from dyck(a+1,b,w+(1,))
 if b<a:yield from dyck(a,b+1,w+(0,))
words=list(dyck());subs={sum(1<<x for x in c):i for i,c in enumerate(itertools.combinations(range(n),k))};perms=[];rows=[];cols=[]
for wi,w in enumerate(words):
 seen=set()
 for trial in range(250):
  hi=list(range(1,6));lo=list(range(6,11));rng.shuffle(hi);rng.shuffle(lo);p=[0]+[hi.pop()if b else lo.pop()for b in w];es=tuple(sorted(sum(1<<p[(i+j)%n]for j in range(k))for i in range(n)))
  if es in seen:continue
  seen.add(es);col=len(perms);perms.append(p)
  for e in es:rows.append(subs[e]);cols.append(col)
  rows.append(len(subs)+wi);cols.append(col)
A=csc_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(subs)+len(words),len(perms)))
print('candidate columns',len(perms),'constraints',A.shape[0],flush=True)
r=milp(np.zeros(len(perms)),integrality=np.ones(len(perms)),bounds=Bounds(0,1),constraints=LinearConstraint(A,1,1),options={'time_limit':100,'threads':2,'disp':True})
print(r,flush=True)
if r.x is not None:
 chosen=[p for p,x in zip(perms,r.x)if x>.5];(D/'outputs/wreath-milp-witness.json').write_text(json.dumps(chosen)+'\n');print('selected',len(chosen),flush=True)

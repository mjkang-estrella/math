import itertools,json,pathlib,time
from scipy.optimize import milp,Bounds,LinearConstraint
import numpy as np
O=pathlib.Path(__file__).resolve().parent
edges=list(itertools.combinations(range(7),3))
def parts(a):
 if len(a)==7:yield a;return
 for c in range(max(a)+2):yield from parts(a+[c])
P=list(parts([0])); A=[]
for a in P:A.append([int(len({a[v] for v in e})!=2) for e in edges])
A+=[[int(v in e) for e in edges] for v in range(7)];A+=[[1]*35]
lo=[1]*len(P)+[4]*7+[10];hi=[np.inf]*(len(P)+7)+[10]
t=time.monotonic();r=milp(np.zeros(35),integrality=np.ones(35),bounds=Bounds(0,1),constraints=LinearConstraint(np.array(A),lo,hi),options={'time_limit':20})
out={'scope':'Exploratory MILP: 7 vertices, 10 triples, degree>=4, every set partition invalidated by an edge. Not an exact infeasibility certificate; source degree reduction not independently proved.','partitions':len(P),'variables':35,'constraints':len(A),'status':int(r.status),'message':r.message,'elapsed':time.monotonic()-t}
if r.x is not None:
 E=[e for e,x in zip(edges,r.x) if x>.5];out['edges']=E;out['exact_uncolorable_check']=all(any(len({a[v] for v in e})!=2 for e in E) for a in P);out['degrees']=[sum(v in e for e in E) for v in range(7)]
(O/'finite-probe.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

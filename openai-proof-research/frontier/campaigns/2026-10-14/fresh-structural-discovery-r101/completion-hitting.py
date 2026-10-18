"""Z3 finite hitting-number screen with explicit witness on success."""
import sys,json,itertools
sys.path.insert(0,'/var/tmp/r101-python');import z3
A=set(map(tuple,json.loads(sys.argv[1])));last=int(sys.argv[2]);S={(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}
shapes=[{((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in S} for k in range(8)]
ts=set()
for sh in shapes:
 for a in A:
  for x,y in sh:
   B=frozenset((u+a[0]-x,v+a[1]-y) for u,v in sh)
   if len(B-A)<=last:ts.add(B)
es=sorted({tuple(sorted(t-A)) for t in ts});V=sorted(set().union(*map(set,es)));vs={v:z3.Bool('v_'+str(i)) for i,v in enumerate(V)}
s=z3.Solver();s.set(timeout=15000)
for e in es:s.add(z3.Or([vs[v] for v in e]))
res=[]
for k in range(0,len(V)+1):
 s.push();s.add(z3.PbLe([(v,1) for v in vs.values()],k));st=s.check();res.append(str(st))
 if st==z3.sat:
  m=s.model();w=[v for v in V if z3.is_true(m.eval(vs[v],model_completion=True))];break
 if st==z3.unknown:w=None;break
 s.pop()
print(json.dumps({'initial':sorted(A),'terminal_budget':last,'targets':len(ts),'vertices':len(V),'checks':res,'minimum':k if str(st)=='sat' else None,'witness':w,'edges':es},indent=2))

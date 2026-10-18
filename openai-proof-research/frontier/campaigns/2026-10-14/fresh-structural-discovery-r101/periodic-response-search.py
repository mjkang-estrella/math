"""Exploratory bounded Z3 search; a SAT witness needs independent exact checking."""
import sys,json,itertools
sys.path.insert(0,'/var/tmp/r101-python')
import z3
P=int(sys.argv[1]);degree=int(sys.argv[2]);timeout=int(sys.argv[3]) if len(sys.argv)>3 else 20000
S={(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}
def orient(s,k):return sorted(((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in s)
shapes=[orient(S,k) for k in range(8)]
diffs=set()
for sh in shapes:
 for a,b in itertools.permutations(sh,2):diffs.add((b[0]-a[0],b[1]-a[1]))
def key(a,b):
 dx,dy=b[0]-a[0],b[1]-a[1]
 return min((a[0]%P,a[1]%P,dx,dy),(b[0]%P,b[1]%P,-dx,-dy))
variables={}
def edge(a,b):
 k=key(a,b)
 if k not in variables:variables[k]=z3.Bool('e_'+'_'.join(map(str,k)))
 return variables[k]
solver=z3.Solver();solver.set(timeout=timeout)
for x in range(P):
 for y in range(P):solver.add(z3.PbLe([(edge((x,y),(x+dx,y+dy)),1) for dx,dy in sorted(diffs)],degree))
# Exclude every partition into connected-component blocks of size at most3.
def partitions(n):
 def rec(blocks,i):
  if i==n:yield [tuple(b) for b in blocks];return
  for b in blocks:
   if len(b)<3:
    b.append(i);yield from rec(blocks,i+1);b.pop()
  blocks.append([i]);yield from rec(blocks,i+1);blocks.pop()
 yield from rec([],0)
parts=list(partitions(6));constraints=0
for x in range(P):
 for y in range(P):
  for sh in shapes:
   a=[(u+x,v+y) for u,v in sh]
   for part in parts:
    labels={j:i for i,block in enumerate(part) for j in block}
    solver.add(z3.Or([edge(a[i],a[j]) for i in range(6) for j in range(i+1,6) if labels[i]!=labels[j]]));constraints+=1
status=solver.check();out={'period':P,'degree':degree,'timeout_ms':timeout,'variables':len(variables),'partitions':len(parts),'component_constraints':constraints,'status':str(status),'limits':'Bounded periodic response-graph screen, not full game classification.'}
if status==z3.sat:
 m=solver.model();out['selected_edges']=[k for k,v in sorted(variables.items()) if z3.is_true(m.eval(v,model_completion=True))]
print(json.dumps(out,indent=2))

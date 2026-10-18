"""Bounded periodic local-priority search; SAT requires separate witness check."""
import sys,json
sys.path.insert(0,'/var/tmp/r101-python')
import z3
P=int(sys.argv[1]);timeout=int(sys.argv[2]) if len(sys.argv)>2 else 20000
D=[(1,0),(0,1),(-1,0),(0,-1)]
S=[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
def orient(s,k):return [((-1 if k&1 else 1)*(y if k&4 else x),(-1 if k&2 else 1)*(x if k&4 else y)) for x,y in s]
solver=z3.Solver();solver.set(timeout=timeout)
ranks={(x,y):[z3.Int(f'r_{x}_{y}_{i}') for i in range(4)] for x in range(P) for y in range(P)}
for rs in ranks.values():solver.add(z3.Distinct(rs),*[z3.And(r>=1,r<=4) for r in rs])
for x in range(P):
 for y in range(P):
  for k in range(8):
   shape=[(a+x,b+y) for a,b in orient(S,k)];ss=set(shape)
   def req(u,v):
    rs=ranks[(u[0]%P,u[1]%P)];iv=D.index((v[0]-u[0],v[1]-u[1]))
    outside=[i for i,d in enumerate(D) if (u[0]+d[0],u[1]+d[1]) not in ss]
    return z3.Sum([z3.If(rs[i]<rs[iv],1,0) for i in outside])<2
   bi=[z3.And(req(shape[i],shape[i+1]),req(shape[i+1],shape[i])) for i in range(5)]
   solver.add(z3.Or([z3.And(bi[i:i+3]) for i in range(3)]))
st=solver.check();out={'period':P,'status':str(st),'limits':'Candidate local-priority rule; no mathematical validation from solver alone.'}
if st==z3.sat:
 m=solver.model();out['directions']=D;out['orders']=[{'cell':xy,'ranks':[m.eval(v).as_long() for v in rs]} for xy,rs in sorted(ranks.items())]
print(json.dumps(out,indent=2))

import itertools,json,pathlib,resource,os
from fractions import Fraction as F
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
# A six-cycle has exactly the diagonal and cyclic perfect matchings.
n=3;edges={(i,i):[10,0,0][i] for i in range(n)};edges.update({(i,(i+1)%n):6 for i in range(n)})
matchings=[[(i,q[i]) for i in range(n)] for q in itertools.permutations(range(n)) if all((i,q[i]) in edges for i in range(n))]
records=[{'edges':m,'sum':sum(edges[e] for e in m),'top2':sum(sorted([edges[e] for e in m],reverse=True)[:2])} for m in matchings]
y={e:F(1,2) for e in edges};x={e:y[e] if edges[e]>0 else F(0) for e in edges}
assert sum(x.values())==2 and all(x[e]<=y[e] for e in edges)
assert all(sum(y[e] for e in edges if e[0]==i)==1 for i in range(n))
assert all(sum(y[e] for e in edges if e[1]==i)==1 for i in range(n))
value=sum(edges[e]*x[e] for e in edges);assert value==14 and max(r['top2'] for r in records)==12
print(json.dumps({'kind':'diagnostic only, no Lean endpoint','six_cycle':records,'fractional_selection_objective':str(value),'fractional_x':{str(e):str(v) for e,v in x.items()},'integral_optimum':12},indent=2))
# Separate wrong whole-perfect-matching shortcut at k=1.
print('k=1 on C4: matching weights (10,0) and (6,6); max-total chooses12 but top1 optimum10 lies in total10 matching.')
# Reproduce only the public SOS construction, not a new result.
counts=[]
for j in range(9):
 a=[j*(8-j)]+[(j-i+1)*(j-i) for i in range(1,9)]
 assert min(a)>=0 and a.count(0)==2
 counts.append(2**sum(v>0 for v in a))
assert sum(counts)==1152
print('Public SOS radicand fibers:',counts,'total',sum(counts),'versus',2**10)
# Verify arithmetic of published EM reduction; this is not algorithm correctness.
for R in range(1,10):
 for k in range(R+1):
  for r in range(R+1):
   weights=sorted([3]*r+[2]*(2*(R-r)+k),reverse=True)
   value=sum(weights[:2*R]); assert (value>=4*R+k)==(r==k)
print('Published EM reduction arithmetic for R<=9 PASS; general proof read separately; bounded test no complexity certificate.')

import itertools,json
# One summand for each edge: its two endpoints remain white and all other
# vertices can independently turn black. Differential over F2 adds one black vertex.
def rank(cols):
 piv={}
 for x in cols:
  while x:
   j=x.bit_length()-1
   if j not in piv:piv[j]=x;break
   x^=piv[j]
 return len(piv)
for n in range(2,13):
 r=n-2;layers=[[m for m in range(1<<r) if m.bit_count()==k] for k in range(r+1)];ranks=[]
 for k in range(r):
  idx={m:i for i,m in enumerate(layers[k+1])}
  ranks.append(rank([sum(1<<idx[m|1<<i] for i in range(r) if not(m>>i&1)) for m in layers[k]]))
 betti=[len(L)-(ranks[k-1] if k else 0)-(ranks[k] if k<r else 0) for k,L in enumerate(layers)]
 print(json.dumps(dict(vertices=n,edge_summand_dimensions=list(map(len,layers)),ranks=ranks,betti=betti,field='F2',semantic_identification='ordinary source-based argument; not Lean certified')),flush=True)

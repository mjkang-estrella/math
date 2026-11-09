import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
ps=list(itertools.permutations(range(4)));tour=[0,9,10,21,17,14,6,1,4,18,3,16,19,2,13,5,23,20,15,8,7,11,22,12];p=[ps[x] for x in tour];N=24
adj=[{} for _ in range(N)]
for i,t in enumerate(p):
 for a in range(4):
  for b in range(4):
   if t[a]<t[b]:adj[(i+a)%N][(i+b)%N]=(i,a,b)
def visit(v,path):
 if v in path:
  cyc=path[path.index(v):]+[v];return cyc
 for w in adj[v]:
  r=visit(w,path+[v])
  if r:return r
 return None
cyc=visit(0,[])
r={'tour_lex_indices':tour,'permutations_1based':[[x+1 for x in t] for t in p],'strict_cycle_positions_0based':cyc,'cycle_edges':[{'from':a,'to':b,'window':adj[a][b][0],'local_offsets':list(adj[a][b][1:])} for a,b in zip(cyc,cyc[1:])]}
(D/'tour-certificate.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))

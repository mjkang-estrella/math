# Independent adjacency-matrix implementation; reads data only.
import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];D=json.loads((L/'outputs/pure-dag.json').read_text());nodes=D['nodes'];bound=D['lower_bound']
for number,node in enumerate(nodes):
 A=node['graph'];n=len(A);assert n>=bound
 assert all(len(r)==n and r[i]==0 and sum(r)==6 and all(r[j]==A[j][i] for j in range(n)) for i,r in enumerate(A))
 legal=[i for i,r in enumerate(A) if sum(v==2 for v in r)==3 and all(v in (0,2) for v in r)]
 assert legal==[x for x,_ in node['children']]
 for x,c in node['children']:
  assert c<number
  V=[i for i in range(n) if i!=x]
  B=[[A[i][j]+int(i!=j and A[x][i]==2 and A[x][j]==2) for j in V] for i in V]
  assert B==nodes[c]['graph']
R=json.loads((L/'outputs/delta-trace-checked.json').read_text())
assert nodes[D['root']]['graph']==R['original']
print('PASS all nodes, all legal pure successors, exact relabelled matrices, closure, bound 11; nodes',len(nodes))

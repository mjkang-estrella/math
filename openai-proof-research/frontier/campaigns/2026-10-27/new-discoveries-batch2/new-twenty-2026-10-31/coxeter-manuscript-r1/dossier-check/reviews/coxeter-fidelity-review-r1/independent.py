from pathlib import Path
import re,ast,json,hashlib,collections
import sympy as sp
w=Path(__file__).resolve().parent; f=w/'fresh'
s=(f/'SpectralDefinitions.lean').read_text(); c=(f/'ConcreteMachine.lean').read_text(); sw=(f/'SpectralWitness.lean').read_text(); results={}
for tag in ['G','H']:
 edges=ast.literal_eval(re.search(r'def edges'+tag+r'.*?:= (.*)',s)[1]); assert len(edges)==18
 adj=[set() for _ in range(19)]
 for a,b in edges: assert 0<=a<19 and 0<=b<19 and a!=b; adj[a].add(b);adj[b].add(a)
 seen={0}; todo=[0]
 while todo:
  for b in adj[todo.pop()]-seen:seen.add(b);todo.append(b)
 assert len(seen)==19 and len({frozenset(e) for e in edges})==18
 A=sp.Matrix(19,19,lambda i,j:int(j in adj[i]));C=sp.ones(19)-sp.eye(19)-A
 L=sp.Matrix(18,18,lambda i,j:int(i!=j and bool(set(edges[i])&set(edges[j]))))
 # Independent forward propagation, constructing reachable states directly from adjacency.
 counts={frozenset():1}; totals=[1]
 for k in range(18):
  nxt=collections.defaultdict(int)
  for state,num in counts.items():
   for a in range(19):
    if a not in state:nxt[frozenset({a}|(state&adj[a]))]+=num
  counts=nxt;totals.append(sum(counts.values()))
 states=ast.literal_eval(re.search(r'def states'+tag+r'.*?:= (.*)',c)[1]); rows=ast.literal_eval(re.search(r'def rows'+tag+r'.*?:= (.*)',c)[1]);assert len(states)==len(rows)==38
 assert len(set(map(tuple,states)))==38 and all(0<=a<19 for t in states for a in t)
 for st,row in zip(states,rows):
  assert len(row)==19
  for a,t in enumerate(row):
   if a in st:assert t==38
   else:assert 0<=t<38 and set(states[t])=={a}|(set(st)&adj[a])
 for k in range(19):
  vector=ast.literal_eval(re.search(r'def v'+tag+str(k)+r' .*?:= \((\[.*?\]) : List Nat\)',c)[1]);assert len(vector)==38
  if k==0:assert vector==[1]*38
  else:assert vector==[sum(prev[t] for t in row if t<38) for row in rows]
  prev=vector
 assert totals[-1]==vector[0]
 matrices={}
 for pfx,mat in [('A',A),('C',C),('L',L)]:
  pp=[]
  for suff in ['P','Q']:
   name=pfx+suff; raw=re.search(r'def '+name+r'\s*:.*?:=\s*!!\[(.*?)\]',sw,re.S)[1]
   vals=[[sp.Rational(x.strip().strip('()')) for x in row.split(',')] for row in raw.split(';')]
   pp.append(sp.Matrix(vals))
  P,Q=pp;assert P*Q==sp.eye(mat.rows) and Q*P==sp.eye(mat.rows)
  matrices[pfx]=(mat,P)
 results[tag]={'edges':edges,'connected':True,'tree':True,'totals_0_to_18':totals,'charpolys':{p:list(map(int,M.charpoly().all_coeffs())) for p,(M,_) in matrices.items()},'states_and_all_transitions_valid':True,'all_backward_vectors_valid':True}
 if tag=='G':gmat=matrices
 else:
  for p,(M,P) in gmat.items():assert M*P==P*matrices[p][0]
for p in ['A','C','L']:assert results['G']['charpolys'][p]==results['H']['charpolys'][p]
results['difference_at_18']=results['G']['totals_0_to_18'][18]-results['H']['totals_0_to_18'][18];assert results['difference_at_18']==4
results['method']='Reviewer-written SymPy exact determinants and rational matrix products, direct adjacency-state forward counting, independent of author generator; parsed frozen literals only.'
(w/'independent-results.json').write_text(json.dumps(results,indent=2));print('PASS trees, all three exact charpolys, all six inverses and three intertwiners, all machine transitions/vectors, forward totals; difference',results['difference_at_18'])

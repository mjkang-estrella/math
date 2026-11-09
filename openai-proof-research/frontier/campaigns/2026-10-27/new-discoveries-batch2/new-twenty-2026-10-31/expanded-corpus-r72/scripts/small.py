import json,pathlib,itertools,math,collections
import sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'vendor'))
import numpy as np,networkx as nx
D=pathlib.Path(__file__).resolve().parents[1]
mode=__import__('sys').argv[1];out={}
if mode=='erasure':
 for r in range(2,5):
  m=r-1; constraints=set(); mats=0
  for cols in itertools.combinations(range(1,2**r),m):
   span={0}
   for c in cols:span|={v^c for v in list(span)}
   if len(span)!=2**m:continue
   mats+=1; hit=sum(1<<(a-1) for a in range(1,2**r) if sum((a&c).bit_count()%2 for c in cols)==1);constraints.add(hit)
  minsize=2**r; valid=0
  for A in range(1<<(2**r-1)):
   if all(A&c for c in constraints):valid+=1;minsize=min(minsize,A.bit_count())
  out[r]=dict(unordered_fullrank_column_sets=mats,distinct_constraints=len(constraints),all_nonzero_subsets=1<<(2**r-1),minimum=minsize,valid_sets=valid)
elif mode=='planar':
 counts=collections.Counter();bad=[]
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<2 or not nx.check_planarity(G)[0]:continue
  counts[n]+=1;A=nx.to_numpy_array(G);L=np.diag(A.sum(1))-A;a=float(np.linalg.eigvalsh(L)[1]);
  if a>3+1e-7 and not (nx.is_isomorphic(G,nx.complete_graph(4)) or nx.is_isomorphic(G,nx.octahedral_graph())):bad.append(dict(n=n,edges=list(G.edges()),a=a,graph6=nx.to_graph6_bytes(G,header=False).decode().strip()))
 out={'atlas_planar_counts':dict(counts),'violations_last_clause':bad,'double_wheels':[]}
 for n in range(3,31):
  G=nx.empty_graph(2);G=nx.disjoint_union(G,nx.cycle_graph(n));G.add_edges_from((i,j) for i in range(2) for j in range(2,n+2));a=float(np.linalg.eigvalsh(np.diag(nx.to_numpy_array(G).sum(1))-nx.to_numpy_array(G))[1]);out['double_wheels'].append(dict(cycle=n,a=a))
elif mode=='latin':
 for n in range(1,5):
  perms=list(itertools.permutations(range(n))); allL=[]
  def rec(rows):
   if len(rows)==n:allL.append(tuple(v for r in rows for v in r));return
   for r in perms:
    if all(all(r[j]!=s[j] for j in range(n)) for s in rows):rec(rows+[r])
  rec([]);reduced=[L for L in allL if list(L[:n])==list(range(n)) and [L[i*n] for i in range(n)]==list(range(n))];res=[]
  for L in reduced:
   c=np.zeros(1<<(n*n),dtype=np.int32)
   for M in allL:c[sum(1<<j for j in range(n*n) if L[j]==M[j])]+=1
   for j in range(n*n):
    step=1<<j
    for base in range(0,len(c),2*step):c[base:base+step]+=c[base+step:base+2*step]
   hist=collections.Counter()
   for mask in range(len(c)):
    if c[mask]==1 and all(c[mask^(1<<j)]>1 for j in range(n*n) if mask>>j&1):hist[mask.bit_count()]+=1
   res.append(dict(square=L,critical_histogram=dict(hist)))
  out[n]=dict(all_latin=len(allL),reduced_count=len(reduced),subsets_each=1<<(n*n),reduced_results=res)
elif mode=='exclusion':
 counts=collections.Counter();worst=0
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<2 or n>5 or not nx.is_connected(G):continue
  counts[n]+=1;L=nx.laplacian_matrix(G).toarray();gap=np.linalg.eigvalsh(L)[1]
  for k in range(1,n):
   states=list(itertools.combinations(range(n),k));idx={s:i for i,s in enumerate(states)};A=np.zeros((len(states),len(states)))
   for s,i in idx.items():
    S=set(s)
    for a,b in G.edges():
     if (a in S)!=(b in S):t=tuple(sorted(S^{a,b}));A[i,i]+=1;A[i,idx[t]]-=1
   worst=max(worst,abs(float(np.linalg.eigvalsh(A)[1])-gap))
 out=dict(connected_unlabeled_graphs=dict(counts),unit_rates_only=True,max_gap_error=worst)
(D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

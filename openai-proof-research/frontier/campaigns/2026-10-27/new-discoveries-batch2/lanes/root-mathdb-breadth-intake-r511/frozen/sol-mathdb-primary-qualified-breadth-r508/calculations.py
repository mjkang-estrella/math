import itertools,json,pathlib
P=pathlib.Path(__file__).resolve().parent
out={'scope':'Finite sanity checks only; no full-scope proof or priority clearance.'}
qs=[]
for n in range(1,6):
 best=0;count=0
 for cols in itertools.product(range(-1,n),repeat=n):
  S=[(r,c) for r,c in enumerate(cols) if c>=0]
  if any(c==d or abs(r-s)==abs(c-d) for (r,c),(s,d) in itertools.combinations(S,2)):continue
  if any(sum(r==a or c==b or abs(r-a)==abs(c-b) for a,b in S) in (2,4) for r in range(n) for c in range(n) if (r,c) not in S):continue
  count+=1;best=max(best,len(S))
 qs.append(dict(n=n,maximum=best,odd_independent_sets=count))
out['queen']=qs
N=5;edges=list(itertools.combinations(range(N),2));tested=0;fails=[]
for mask in range(1<<len(edges)):
 E=[e for i,e in enumerate(edges) if mask>>i&1];seen={0}
 while True:
  more=seen|{v for a,b in E for u,v in [(a,b),(b,a)] if u in seen}
  if more==seen:break
  seen=more
 if len(seen)<N:continue
 tested+=1;cuts=[sum(((s>>a)&1)!=((s>>b)&1) for a,b in E) for s in range(1<<N)]
 EP=[min(cuts[s] for s in range(1<<N) if s>>a&1 and not s>>b&1) for a,b in edges]
 even=all(sum(v in e for e in E)%2==0 for v in range(N))
 if even!=all(p%2==0 for p in EP):fails.append(mask)
 for q in range(1,N):
  if max(EP)<=q and 2*len(E)>(q+1)*(N-1):fails.append([mask,q])
out['edge_path']={'connected_labeled_graphs_n5':tested,'failures':fails}
out['binary_square_free_length4']=[list(w) for w in itertools.product(range(2),repeat=4) if all(w[i:i+k]!=w[i+k:i+2*k] for k in [1,2] for i in range(5-2*k))]
assert not out['binary_square_free_length4'] and not fails and all(x['maximum']==1 for x in qs)
(P/'calculation-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

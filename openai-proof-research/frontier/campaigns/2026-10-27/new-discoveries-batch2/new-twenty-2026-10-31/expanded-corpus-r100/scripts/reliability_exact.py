import json,itertools,math
out=[]
for row in json.load(open('outputs/reliability.json')):
 n=row['n']
 if n not in [10,12]:continue
 base=[(i,(i+1)%n) for i in range(n)];graphs=[base+[(i,i+n//2) for i in range(n//2)],base+row['matching']];cs=[]
 for edges in graphs:
  counts=[0]*(len(edges)+1)
  for size in range(n-1,len(edges)+1):
   for sub in itertools.combinations(range(len(edges)),size):
    par=list(range(n))
    def root(x):
     while par[x]!=x:x=par[x]
     return x
    for k in sub:
     a,b=edges[k];par[root(a)]=root(b)
    if all(root(i)==root(0) for i in range(n)):counts[size]+=1
  cs.append(counts)
 print('n',n,'FCG',cs[0],'competitor',cs[1],flush=True)
 assert cs[0][n-1]==row['FCG_trees'] and cs[1][n-1]==row['best_trees']
 out.append(dict(n=n,edges=graphs,connected_subsets_by_edge_count=cs,componentwise_dominates=all(a<=b for a,b in zip(*cs))))
 json.dump(out,open('outputs/reliability-exact.json','w'),indent=2)

from bme_search import *
from ubb_search import connected

def valid(E,n):
 a=adj(E)
 assert len(E)==2*n-3 and len(a)==2*n-2
 assert len(set(E))==len(E)
 assert all(len(a[i])==1 for i in range(n))
 assert all(len(v)==3 for k,v in a.items() if k<0)
 assert connected_graph(a)

def connected_graph(a):
 seen=set();stack=[next(iter(a))]
 while stack:
  x=stack.pop()
  if x in seen:continue
  seen.add(x);stack.extend(a[x])
 return len(seen)==len(a)

out={}
for n in [7,8]:
 ts=trees(n);keys=set()
 for E in ts:
  valid(E,n);keys.add(canon(E,n));w=weights(E,n);rows=[0]*n
  for v,(i,j) in zip(w,combinations(range(n),2)):rows[i]+=v;rows[j]+=v
  assert rows==[2**(n-2)]*n
 assert len(keys)==len(ts)
 E=ts[len(ts)//2];near=tbr(E,n)
 for G in near.values():valid(G,n);assert canon(G,n) in keys
 out[str(n)]={'valid_binary_trees_and_distinct_split_keys':len(ts),'sample_TBR_outputs_valid':len(near),'kraft_row_sums':True}
rs=json.loads((P/'ubb-runs.json').read_text())['graphs']
for r in rs:
 n=r['n'];es=r['edges'];m=len(es)
 assert min(sum(((s>>u)^(s>>v))&1 for u,v in es) for s in range(1,1<<(n-1)))==r['lambda']
 fam=r['family_masks'];assert len(fam)<=m
 for t in fam:
  assert 0<=t<(1<<m) and t.bit_count()==n-1
  assert connected(n,[e for i,e in enumerate(es) if t>>i&1])
 for cs in combinations(range(m),r['lambda']-1):
  f=sum(1<<i for i in cs);assert any(t&f==0 for t in fam)
out['ubb']={'fresh_exact_validation_graphs':len(rs),'all_failure_sets_covered':True,'all_families_at_most_edges':True}
(P/'experiment-validation.json').write_text(json.dumps(out,indent=2));print(out)

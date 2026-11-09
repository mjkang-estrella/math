import pathlib,json,collections,itertools
D=pathlib.Path(__file__).resolve().parents[1];ns={'__file__':str(D/'scripts/tree_refine.py')};exec((D/'scripts/tree_refine.py').read_text().split('raw=json.loads')[0],ns)
# Cross-check full-cover edge IE against direct walk enumeration on every tree through order 5.
for n in range(2,6):
 data=json.loads((D/f'tree-survivors-{n}.json').read_text())
 # Build all rooted tree codes through n anew in a tiny independent leaf extension.
 if n==2:codes={((),)}
 else:
  new=set()
  for c in codes:
   g=ns['graph'](c)
   for v in range(n-1):
    g[v].append(n-1);g.append([v]);new.add(ns['canonical'](g));g.pop();g[v].pop()
  codes=new
 for c in codes:
  g=ns['graph'](c);edges={tuple(sorted((u,v))):0 for u in range(n) for v in g[u] if u<v};edges={e:i for i,e in enumerate(edges)};co=ns['coeffs'](g);seq=[0]*13
  for p,v in co.items():
   for k,z in enumerate(ns['moments'](p,12)):seq[k]+=v*z
  direct=[0]*13
  for start in range(n):
   dp={(start,0):1}
   for d in range(1,13):
    nxt=collections.Counter()
    for (u,mask),num in dp.items():
     for v in g[u]:nxt[v,mask|1<<edges[tuple(sorted((u,v)))]]+=num
    dp=nxt;direct[d]+=dp.get((start,(1<<(n-1))-1),0)
  assert seq[1:]==direct[1:],(c,seq,direct)
print('direct-walk/edge-IE validation all unlabelled trees orders2..5 length1..12 passed',flush=True)
out=[]
for n in range(2,18):
 raw=json.loads((D/f'tree-survivors-{n}.json').read_text());surv=[]
 for bucket in raw['canonical_rooted_codes']:
  groups=collections.defaultdict(list)
  for c in bucket:
   c=ns['tuples'](c);co=ns['coeffs'](ns['graph'](c));seq=[0]*103
   for p,v in co.items():
    for i,z in enumerate(ns['moments'](p,102)):seq[i]+=v*z
   groups[tuple(seq)].append(c)
  surv.extend(v for v in groups.values() if len(v)>1)
 row={'n':n,'input_buckets':len(raw['canonical_rooted_codes']),'full_cover_through102_surviving_buckets':len(surv),'survivors':surv};out.append(row);print(json.dumps({'n':n,'surviving':len(surv)}),flush=True);(D/'tree-refined-all.json').write_text(json.dumps(out,indent=2)+'\n')

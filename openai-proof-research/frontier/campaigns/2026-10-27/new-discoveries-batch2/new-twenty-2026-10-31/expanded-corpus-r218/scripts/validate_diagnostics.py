import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];ns={'__file__':str(D/'scripts/trees.py')};exec(compile((D/'scripts/trees.py').read_text().split("level={'()'")[0],str(D/'scripts/trees.py'),'exec'),ns)
level={'()':[[]]};tested=0
for n in range(2,10):
 nxt={}
 for a in level.values():
  for v in range(n-1):
   b=[x.copy() for x in a]+[[v]];b[v].append(n-1);nxt[ns['canonical'](b)]=b
 level=nxt
 for a in level.values():
  es=[(u,v) for u in range(n) for v in a[u] if u<v];count=total=0
  for s in range(1<<len(es)):
   verts=[]
   for j,e in enumerate(es):
    if s>>j&1:verts.extend(e)
   if len(verts)!=len(set(verts)):continue
   if any(u not in verts and v not in verts for u,v in es):continue
   count+=1;total+=s.bit_count()
  assert (count,total)==ns['moments'](a),(n,a,(count,total),ns['moments'](a));tested+=1
assert [len(x) for x in level.values()]==[9]*47
out={'tree_moment_DP_independent_matching_enumeration':'pass','all_unlabelled_orders_2_to_9':tested,'generator_counts_order9':len(level),'warning':'diagnostic validation, not a Lean certificate'}
(D/'logs/diagnostic-validation.json').write_text(json.dumps(out,indent=2));print(out)

import pathlib,json,itertools,resource,os,functools,time
os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_CPU,(100,100));resource.setrlimit(resource.RLIMIT_AS,(2200*1024**2,2200*1024**2))
l=pathlib.Path(__file__).parent;t=time.monotonic()
o=json.loads((l/'bicommutative-search.json').read_text());f=[frozenset(i for i in range(15) if x>>i&1) for x in o['best_masks']]
universe=list(map(frozenset,itertools.combinations(range(15),7)))
assert len(set(f))==1505 and all(len(s)==7 for s in f)
assert all(s&t for s,t in itertools.combinations(f,2))
fs=set(f);cover={}
for s in universe:
 if s not in fs:
  witness=next(t for t in f if not(s&t));cover[str(sum(1<<i for i in s))]=sum(1<<i for i in witness)
fano=list(map(frozenset,[(8,9,12),(8,10,13),(8,11,14),(9,10,14),(10,11,12),(12,13,14),(9,11,13)]))
source=[s for s in universe if len(s&frozenset(range(8,15)))<=2 or (s&frozenset(range(8,15))) in fano]
assert len(source)==1870
(l/'bicommutative-cover.json').write_text(json.dumps(cover,sort_keys=True)+'\n')
# Independent Candy Nim recursion uses fixed labeled piles including zeros, no
# sorting or quotient. Value is the score difference, rather than W recurrence.
@functools.lru_cache(None)
def value(g):
 if not any(g):return 0
 xor=functools.reduce(int.__xor__,g,0)
 if xor:
  return min(-(a-(a^xor))+value(g[:i]+(a^xor,)+g[i+1:]) for i,a in enumerate(g) if a^xor<a)
 return max((a-b)+value(g[:i]+(b,)+g[i+1:]) for i,a in enumerate(g) for b in range(a))
vals={str(g):value(g) for g in [(3,4,7),(1,2,4,7),(3,5,6),(1,2,5,6),(12,20,24),(4,8,20,24)]}
assert vals['(12, 20, 24)']==38 and vals['(4, 8, 20, 24)']==36
# A full state/value table is a replayable Bellman certificate, not Lean proof.
# Python cache cannot be enumerated; enumerate the entire rectangular domains
# (including states not required by an optimal strategy) to retain all values.
tables={}
for bounds in [(12,20,24),(4,8,20,24)]:
 rows=[]
 for g in itertools.product(*(range(a+1) for a in bounds)):
  rows.append(value(g))
 tables[','.join(map(str,bounds))]={'dimensions':[a+1 for a in bounds],'values_lexicographic':rows}
(l/'candy-bellman-tables.json').write_text(json.dumps(tables)+'\n')
(l/'candidate-validation.json').write_text(json.dumps({'bicomm':{'family_size':len(f),'source_family_size':len(source),'seven_subsets':len(universe),'outside_dominated':len(cover),'direct_set_pair_checks':1505*1504//2},'candy':{'independent_labeled_score_values':vals,'memo':str(value.cache_info()),'table_state_count':sum(len(v['values_lexicographic']) for v in tables.values())},'wall_seconds':time.monotonic()-t},indent=2)+'\n')
print((l/'candidate-validation.json').read_text())

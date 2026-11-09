import itertools,collections,math,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1]
def pattern(x):return tuple(sorted(range(len(x)),key=lambda j:x[j]).index(i) for i in range(len(x)))
rows=[]
for k in range(3,6):
 pats=list(itertools.permutations(range(k)));h={p:[] for p in pats}
 for n in range(k,10):
  counters={p:collections.Counter() for p in pats}
  for perm in itertools.permutations(range(n)):
   counts=collections.Counter(pattern(perm[i:i+k]) for i in range(n-k+1))
   for p,c in counts.items():counters[p][c]+=1
  for p in pats:
   co=counters[p];co[0]=math.factorial(n)-sum(co.values());h[p].append(tuple(co[i] for i in range(n-k+2)))
 groups=collections.defaultdict(list)
 for p in pats:groups[tuple(row[0] for row in h[p])].append(p)
 splits=[]
 for g in groups.values():
  if len({tuple(h[p]) for p in g})>1:splits.append(g)
 rows.append({'pattern_length':k,'permutation_orders':list(range(k,10)),'avoidance_signature_classes':len(groups),'classes_splitting_by_occurrence_distribution':splits,'scope':'bounded agreement only; avoidance equality for all orders is not established'})
(D/'outputs/patterns.json').write_text(json.dumps(rows,indent=2));print(rows)

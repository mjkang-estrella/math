import itertools,collections,json
# Full ordered alphabet-surjectivity; scattered subsequence order-isomorphism.
def words(n):
 for k in range(1,n+1):
  for w in itertools.product(range(1,k+1),repeat=n):
   if len(set(w))==k:yield w
def std(w):
 d={x:i+1 for i,x in enumerate(sorted(set(w)))};return tuple(d[x] for x in w)
for m in [3,4]:
 pats=list(words(m)); counts={p:[] for p in pats}
 for n in [m,m+1,m+2]:
  c=collections.Counter();total=0
  for w in words(n):
   total+=1
   contained={std(tuple(w[i] for i in inds)) for inds in itertools.combinations(range(n),m)}
   c.update(contained)
  for p in pats:counts[p].append(total-c[p])
 groups=collections.defaultdict(list)
 for p,v in counts.items():groups[tuple(v)].append(p)
 cross=[{'counts':v,'patterns':p} for v,p in groups.items() if len({max(x) for x in p})>1]
 print(json.dumps({'length':m,'tested_avoidance_lengths':list(range(m,m+3)),'patterns':len(pats),'cross_maximum_finite_matches':cross,'limit':'Finite separation cannot establish all-length equivalence or the universal conjecture.'}),flush=True)

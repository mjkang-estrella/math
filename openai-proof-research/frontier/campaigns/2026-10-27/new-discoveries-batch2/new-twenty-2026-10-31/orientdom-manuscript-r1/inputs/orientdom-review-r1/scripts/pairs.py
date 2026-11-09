from itertools import product,combinations
count=flips=0
for n in range(1,6):
 edges=list(combinations(range(n),2));groups={}
 for digits in product(range(3),repeat=len(edges)):
  inc=[0]*n;g=0
  for i,((a,b),v) in enumerate(zip(edges,digits)):
   if v:g|=1<<i
   if v==1:inc[b]|=1<<a
   if v==2:inc[a]|=1<<b
  if not all(inc):continue
  td=[s for s in range(1<<n) if all(s&x for x in inc)]
  groups.setdefault(g,[]).append((inc,td))
 for values in groups.values():
  for D,sets in values:
   for E,_ in values:
    rev=[(a,b) for b in range(n) for a in range(n) if D[b]>>a&1 and not E[b]>>a&1]
    safe=[(a,b,w) for a,b in rev for w in range(n) if w!=a and D[b]>>w&1]
    for S in sets:
     count+=1;target=all(S&x for x in E)
     assert safe or target
     for a,b,w in safe:
      F=D.copy();F[b]^=1<<a;F[a]|=1<<b
      assert all(F) and all((S|1<<w)&x for x in F)
      new=sum((F[v]&~E[v]).bit_count() for v in range(n))
      assert new==len(rev)-1;flips+=1
print({'all_TD_set_ordered_pair_checks_n_le_5':count,'safe_flip_witness_checks':flips,'failures':0})

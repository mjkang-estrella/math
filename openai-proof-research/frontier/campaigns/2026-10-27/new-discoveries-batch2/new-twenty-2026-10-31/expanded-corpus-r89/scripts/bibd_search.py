import itertools,json
# Enumerate all equipartitions of the 16-point quadratic Menon design.
pts=set(range(16));q=lambda x:((x&1)*((x>>1)&1))^(((x>>2)&1)*((x>>3)&1))
blocks=[{x for x in pts if q(x^a)} for a in pts];count=0;survive=0;example=None
# A colour class has size four, and meets each block in zero or two points.
classes=[frozenset(c) for c in itertools.combinations(range(16),4) if all(len(set(c)&b) in [0,2] for b in blocks)]
def rec(rem,chosen):
 global count,survive,example
 if not rem:
  count+=1
  if all(sorted(len(c&b) for c in chosen)==[0,2,2,2] for b in blocks):survive+=1;example=[sorted(c) for c in chosen]
  return
 x=min(rem)
 for c in classes:
  if x in c and c<=rem:rec(rem-c,chosen+[c])
rec(frozenset(pts),[])
print(json.dumps(dict(design=[16,6,2],ell=4,all_four_subsets=1820,admissible_colour_classes=len(classes),candidate_partitions=count,ULSE_partitions=survive,witness=example)),flush=True)

import itertools,json,collections
pairs=list(itertools.combinations(range(4),2));out={}
for mask in [31,55]:
 E={e for k,e in enumerate(pairs) if mask>>k&1};hist=collections.Counter();poly=collections.Counter()
 assert all((u,w) in E for u,v in E for x,w in E if x==v)
 for p in itertools.permutations(range(4)):
  desc=tuple(i for i in range(3) if (p[i],p[i+1]) in E);hist[sum(1<<i for i in desc)]+=1
  for xs in itertools.combinations_with_replacement(range(4),4):
   if all(xs[i]<xs[i+1] for i in desc):poly[tuple(xs.count(i) for i in range(4))]+=1
 mins=[u for u in range(4) if not any(v==u for _,v in E)];maxs=[u for u in range(4) if not any(v==u for v,_ in E)]
 out[str(mask)]=dict(edges=sorted(E),minimal=mins,maximal=maxs,sum_minmax=len(mins)+len(maxs),F_signature=[hist[i] for i in range(8)],monomial_four_variable_coefficients={str(k):v for k,v in sorted(poly.items())})
assert out['31']['F_signature']==out['55']['F_signature']
assert out['31']['monomial_four_variable_coefficients']==out['55']['monomial_four_variable_coefficients']
print(json.dumps(out,indent=2))

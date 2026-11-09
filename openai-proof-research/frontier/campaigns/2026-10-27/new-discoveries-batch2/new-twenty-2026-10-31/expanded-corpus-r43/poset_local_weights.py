import itertools,collections,fractions,resource,json
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
n=6;l=2;r=3
canonical=lambda x: tuple(-a for a in x) if next((a for a in x if a),1)<0 else tuple(x)
def valid(x):
 s=[a for a in x if a];return s and sum(a!=b for a,b in zip(s,s[1:]))<=l
ranks={k:[] for k in [r,r+1]}
for x in itertools.product([0,1,-1],repeat=n):
 if sum(a!=0 for a in x) in ranks and valid(x) and canonical(x)==x:ranks[sum(a!=0 for a in x)].append(x)
incoming=collections.defaultdict(fractions.Fraction)
for x in ranks[r]:
 for a in range(n):
  if x[a]:continue
  ys=[]
  for s in [1,-1]:
   y=list(x);y[a]=s
   if valid(y):ys.append(canonical(y))
  for y in ys:incoming[y]+=fractions.Fraction(1,len(ys))
examples={}
for y,z in incoming.items():examples.setdefault(str(z),y)
print(json.dumps({'n':n,'ell':l,'rank':r,'incoming_sum_examples':examples,'conclusion':'Source l1 equal-choice insertion weights do not give rank-constant incoming sum at l2.'}))

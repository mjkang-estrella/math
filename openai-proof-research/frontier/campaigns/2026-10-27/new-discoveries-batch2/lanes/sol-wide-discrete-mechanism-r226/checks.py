import itertools,json
from pathlib import Path
L=Path(__file__).parent
def mul(a,b):
 return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def wielandt(n):
 b=[[0]*n for _ in range(n)]
 for i in range(n-1):b[i][i+1]=1
 b[-1][0]=b[-1][1]=1
 return b
out={'matrix_exponents':[],'support_families':[]}
for n in range(3,13):
 b=wielandt(n);p=b;counts=[]
 for k in range(1,(n-1)**2+2):
  counts.append(sum(x==0 for r in p for x in r))
  if not counts[-1]:break
  p=mul(p,b)
 assert k==(n-1)**2+1
 out['matrix_exponents'].append({'n':n,'exponent':k,'zero_counts':counts})
for n in [3,4]:
 b=wielandt(n)
 for d in [2,3]:
  # Each family is EXACTLY all possible root supports of depth-k leaf words.
  f={1<<i for i in range(n)};trace=[sorted(f)]
  while f!={(1<<n)-1}:
   new=set()
   for ss in itertools.product(f,repeat=d):
    r=0
    for i in range(n):
     if all(ss) and any(b[i][j] and (ss[0]>>j&1) for j in range(n)):r|=1<<i
    new.add(r)
   f=new;trace.append(sorted(f))
   assert len(trace)<20
  assert len(trace)-1==(n-1)**2+1
  out['support_families'].append({'n':n,'order':d+1,'trace':trace})
# Petersen conference matrix: vertices are pairs of a five-set, edges disjoint.
v=list(itertools.combinations(range(5),2));c=[[0 if i==j else ( -1 if set(x).isdisjoint(y) else 1) for j,y in enumerate(v)] for i,x in enumerate(v)]
assert mul(c,c)==[[9*int(i==j) for j in range(10)] for i in range(10)]
assert {sum(r) for r in c}=={3}
out['conference_route']={'order':10,'square':9,'row_sum':3,'odd_blowup_t3_row_sum':7,'status':'fails to obstruct regular switching'}
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'matrix_cases':10,'exact_support_cases':4,'n3_exponent':5,'conference_row_sum':3}))

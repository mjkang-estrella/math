import resource,signal,itertools,math,json
from collections import Counter
from fractions import Fraction as Q
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(35)
def mul(a,b):return tuple(a[b[i]] for i in range(5))
e=tuple(range(5))
def order(a):
 b=e
 for k in range(1,61):
  b=mul(b,a)
  if b==e:return k
 raise AssertionError
A=[p for p in itertools.permutations(range(5)) if sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))%2==0]
assert len(A)==60
cnt=Counter(map(order,A));assert cnt=={1:1,2:15,3:20,5:24}
inv={a:tuple(a.index(i) for i in range(5)) for a in A}; unseen=set(A);sizes=[]
while unseen:
 a=next(iter(unseen));c={mul(mul(g,a),inv[g]) for g in A};sizes.append(len(c));unseen-=c
assert sorted(sizes)==[1,12,12,15,20]
assert all(60%(1+sum(S))!=0 or 1+sum(S) in [1,60] for r in range(5) for S in itertools.combinations([12,12,15,20],r))
# Nontrivial-shift coset in A5 wr C2. Its square is (ab,ba).
coset=Counter(2*order(mul(a,b)) for a in A for b in A)
assert coset==Counter({2:60,4:900,6:1200,10:1440})
# Exact lcm distribution of independent uniform A5 products, no giant wreath enumeration.
d={1:1}; rows=[]
for s in range(1,17):
 new=Counter()
 for a,v in d.items():
  for b,w in cnt.items():new[math.lcm(a,b)]+=v*w
 d=new
 assert sum(d.values())==60**s
 if s in [1,2,4,8,16]:
  t=2*s; bound=(1-Q(1,t))*(1-Q(3,4)**s-Q(2,3)**s-Q(3,5)**s)
  exact=(1-Q(1,t))*Q(d.get(30,0),60**s)
  assert exact>=bound
  if s>=8:assert bound>Q(1,2)
  rows.append({'t':t,'rho60_exact':str(exact),'lower_bound':str(bound)})
# Independent primitive-order and Held-Karp cycle census at eleven.
prim={x for x in range(1,11) if len({pow(x,j,11) for j in range(10)})==10}
assert prim=={2,6,7,8}
adj={x:{y for y in range(1,11) if x!=y and (2+x*y)%11 in prim} for x in range(1,11)}
assert adj[2]==adj[9]=={3,8}
dp={(1,0):1}
for mask in range(1,1<<10):
 for v in range(10):
  count=dp.get((mask,v),0)
  if count:
   for w in adj[v+1]:
    j=w-1
    if not mask>>j&1:dp[(mask|1<<j,j)]=dp.get((mask|1<<j,j),0)+count
cycles=sum(dp.get((1023,v),0) for v in range(1,10) if 1 in adj[v+1]);assert cycles==0
# C3 + C1 extended-Stanley public counterexample.
rowsP=[p for p in itertools.permutations(range(4)) if p.index(0)<p.index(1)<p.index(2)]
mins=Counter(min(p.index(2)+1,p.index(3)+1) for p in rowsP)
assert mins=={1:1,2:1,3:2} and mins[2]**2<mins[1]*mins[3]
print(json.dumps({'A5_orders':dict(cnt),'A5_class_sizes':sorted(sizes),'wreath_coset_orders':dict(coset),'lcm_rows':rows,'public_sun_adjacency':{str(x):sorted(v) for x,v in adj.items()},'sun_hamilton_cycles':cycles,'public_poset_min_counts':dict(mins),'status':'PASS'},indent=2))

import resource,signal,time,itertools,math,json,pathlib,collections
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(30)
start=time.monotonic();O=pathlib.Path(__file__).resolve().parent
# Independent route: generate A5 by two 3-cycles, rather than filtering S5.
e=tuple(range(5))
def mul(a,b):return tuple(a[b[i]] for i in range(5))
def inv(a):return tuple(a.index(i) for i in range(5))
gens=[(1,2,0,3,4),(0,1,3,4,2)];S={e}; todo=[e]
while todo:
 a=todo.pop()
 for b in gens:
  c=mul(a,b)
  if c not in S:S.add(c);todo.append(c)
assert len(S)==60
# Cycle decomposition order, no repeated-power order algorithm.
def order(p):
 seen=set();v=1
 for i in range(5):
  if i in seen:continue
  n=0;j=i
  while j not in seen:seen.add(j);n+=1;j=p[j]
  v=math.lcm(v,n)
 return v
counts=collections.Counter(map(order,S));assert counts=={1:1,2:15,3:20,5:24}
classes={frozenset(mul(mul(g,a),inv(g)) for g in S) for a in S}; sizes=sorted(map(len,classes));assert sizes==[1,12,12,15,20]
assert not [1+sum(v for i,v in enumerate([12,12,15,20]) if mask>>i&1) for mask in range(1,15) if 60%(1+sum(v for i,v in enumerate([12,12,15,20]) if mask>>i&1))==0]
# Independent exact route: divisor-lattice Mobius inversion, integer counts.
def exact(s):
 return sum((-1)**sum(mask>>i&1 for i in range(3)) * sum(c for d,c in counts.items() if (30//math.prod([p for i,p in enumerate([2,3,5]) if mask>>i&1]))%d==0)**s for mask in range(8))
# Cross-check occupancy by inclusion-exclusion on the 3 distinct order species.
from fractions import Fraction as F
rows=[]
for s in [1,2,3,4,8,16,32]:
 x=exact(s); q=F(x,60**s); assert 0<=q<=1
 ub=1-F(3,4)**s-F(2,3)**s-F(3,5)**s;assert q>=ub
 rows.append({'s':s,'exact_count':str(x),'probability':str(q),'union_lower':str(ub)})
s=8;t=16;rho=F(15,16)*F(exact(s),60**s);lower=F(15,16)*(1-F(3,4)**8-F(2,3)**8-F(3,5)**8)
assert rho>=lower>F(5,8)>F(1,2)
# Bijection diagnostic: each chosen first entry and desired product yields one second entry.
for a in S:
 for p in S:assert mul(a,mul(inv(a),p))==p
# Minimal normal logic proved in review; no giant group enumeration.
# Example 2.8 standard A5 wreath C2: unique index-2 subgroup must be base.
base24=F(sum(c for d,c in counts.items() if 24%d==0),60)**2;assert base24==F(9,25)
# Full wreath has half base and half nonzero component; latter order=2 ord(product).
full24=(base24+F(sum(c for d,c in counts.items() if 12%d==0),60))/2;assert full24==F(12,25)
result={'status':'PASS','route':'two-generator closure; cycle orders; Mobius integer inversion','order_counts':dict(counts),'class_sizes':sizes,'lcm':rows,'rho60star_m4':str(rho),'lower_m4':str(lower),'base_rho24':str(base24),'full_wreath_rho24':str(full24),'wall_seconds':time.monotonic()-start,'maxrss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'limits':{'AS_MiB':512,'CPU_seconds':20,'alarm_seconds':30,'external_wall_seconds':35,'BLAS_threads':1},'all_m_proof':'review.md; finite checks alone do not prove infinite family'}
(O/'checker-results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

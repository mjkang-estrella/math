import itertools,json,math,resource,pathlib,time
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
L=pathlib.Path(__file__).resolve().parent
# Integral determinant via permutation formula, no float inference.
def det(a):
 n=len(a)
 return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*math.prod(a[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
print('DETERMINANT: exhaustive n=4 Gram bounds for k=1 and 2; diagnostic natural interpretation m_k=m1, m_(k+1)=m2',flush=True)
rows=list(itertools.product([0,1],repeat=4))
for k in [1,2]:
 rs=[r for r in rows if sum(r)==k]
 for m in range(1,4):
  gmax=0
  for a in itertools.product(rs,repeat=m):gmax=max(gmax,det([[sum(x*y for x,y in zip(r,s)) for s in a] for r in a]))
  print({'weight':k,'row_count':m,'max_Gram_determinant':gmax},flush=True)
a=[[0,1,1,0],[1,0,1,0],[1,1,0,0],[0,0,0,1]]
print({'witness':a,'ones':sum(map(sum,a)),'det':det(a),'n':4,'tilde_k':'7/4','gamma':'3/4','m1':1,'m2':3,'natural_interpolated_rhs':'2^(3/4)','exact_failure_power4':'16 > 8'},flush=True)
# exhaustive small unbalanced products, closed-neighborhood definition exactly.
print('IRREDUNDANCE: all integer partitions of each factor size 2..4, two factors, labelled canonical blocks',flush=True)
def parts(n,lo=1):
 if n==0:yield ()
 for x in range(lo,n+1):
  for p in parts(n-x,x):yield (x,)+p
def labels(p):return tuple(i for i,n in enumerate(p) for _ in range(n))
ps=[p for n in range(2,5) for p in parts(n) if len(p)>=2]
for p,q in itertools.combinations_with_replacement(ps,2):
 vs=list(itertools.product(labels(p),labels(q)));n=len(vs)
 ns=[sum(1<<j for j,w in enumerate(vs) if i==j or all(a!=b for a,b in zip(v,w))) for i,v in enumerate(vs)]
 alpha=ir=0
 for s in range(1,1<<n):
  size=s.bit_count()
  if size<=min(alpha,ir):continue
  chosen=[i for i in range(n) if s>>i&1]
  if all(ns[i]&s==1<<i for i in chosen):alpha=max(alpha,size)
  if size>ir and all(any(ns[w]&s==1<<i for w in range(n) if ns[i]>>w&1) for i in chosen):ir=size
 print({'factors':[p,q],'vertices':n,'alpha':alpha,'IR':ir},flush=True)

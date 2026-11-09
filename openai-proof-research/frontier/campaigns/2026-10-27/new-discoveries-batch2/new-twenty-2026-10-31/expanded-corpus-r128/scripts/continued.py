import pathlib,itertools,collections,math,sys
D=pathlib.Path(__file__).resolve().parents[1]
def chi(a):
 u,v,w,z=1,0,0,1
 for x in a:u,v,w,z=v,u+v*x,z,w+z*x
 return (v+z)*(w+z)
for n,N in [(4,25),(5,15),(6,12),(7,10),(8,9)]:
 good=bad=0
 for c in itertools.combinations(range(1,N+1),n):
  vals=set();fail=False
  for a in itertools.permutations(c):
   if a[0]>a[-1]:continue
   v=chi(a)
   if v in vals:fail=True;break
   vals.add(v)
  bad+=fail;good+=not fail
 print(dict(n=n,N=N,tuples=good+bad,nontrivial=bad,qualification='complete distinct-digit subsets, all orderings modulo reversal until a collision'),flush=True)
# Independently expand the continuant via its recurrence as a sparse polynomial.
def add(a,b):return dict(collections.Counter(a)+collections.Counter(b))
def mul(a,b):
 o=collections.Counter()
 for x,c in a.items():
  for y,d in b.items():o[tuple(v+w for v,w in zip(x,y))]+=c*d
 return dict(o)
for n in range(3,11):
 zero=(0,)*n
 def K(order):
  a={zero:1};b={zero:1}
  if not order:return b
  b={tuple(int(j==order[0])for j in range(n)):1}
  for i in order[1:]:a,b=b,add(mul({tuple(int(j==i)for j in range(n)):1},b),a)
  return b
 order=tuple(range(n));Q=K(order);P=K(order[1:]);R=K(order[:-1]);C=mul(add(Q,P),add(Q,R))
 for i in range(n):
  exp=[2]*n;exp[i]-=1;assert C.get(tuple(exp),0)==int(i in (0,n-1))
 for i in range(n):
  for j in range(i+1,n):
   exp=[2]*n;exp[i]-=1;exp[j]-=1
   assert C.get(tuple(exp),0)==2*int(j==i+1)+int(i==0 and j==n-1)
 print(dict(symbolic_n=n,monomials=len(C),endpoint_and_adjacency_coefficients='PASS'),flush=True)

import itertools,json
from pathlib import Path
L=Path(__file__).resolve().parent;p=3
def mul(a,b):
 return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%p for i in range(2) for j in range(2))
def add(a,b):return tuple((x+y)%p for x,y in zip(a,b))
def tensor(a,b):return tuple(x*y%p for x in a for y in b)
def rank_add(v,B):
 v=list(v)
 for i,b in sorted(B.items()):
  if v[i]:
   c=v[i];v=[(x-c*y)%p for x,y in zip(v,b)]
 if not any(v):return
 i=next(i for i,x in enumerate(v) if x);c=pow(v[i],-1,p);B[i]=[x*c%p for x in v]
A=list(itertools.product(range(p),repeat=4));K={};J={};cp=cj=0
for a in A:
 for b in A:
  ab=mul(a,b);ba=mul(b,a);v=tensor(a,b)
  if not any(ab):rank_add(v,K);cp+=1
  if not any(add(ab,ba)):rank_add(v,J);cj+=1
assert len(K)==len(J)==12
u=(1,0,0,2);v=(0,1,0,0);e=(1,0,0,0)
assert add(mul(u,v),mul(v,u))==(0,0,0,0)
assert add(mul(mul(e,u),v),mul(v,mul(e,u)))==v
# The ordinary zero-product relation space is not flip invariant.
x=(0,1,0,0);y=e
assert not any(mul(x,y)) and mul(y,x)==x
# Dual numbers F3[t]/(t^2): tensor dimension4, multiplication rank2.
D=list(itertools.product(range(p),repeat=2));KD={};JD={}
def dm(a,b):return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)
for a in D:
 for b in D:
  if not any(dm(a,b)):rank_add(tensor(a,b),KD);rank_add(tensor(a,b),JD)
assert len(KD)==len(JD)==1
f=lambda a,b:a[0]*b[1]%p
assert all(not f(a,b) for a in D for b in D if not any(dm(a,b)))
assert f((1,0),(0,1))==1 and f((0,1),(1,0))==0
r=dict(status='PASS',field=3,matrix_pairs=len(A)**2,ordinary_zero_pairs=cp,jordan_zero_pairs=cj,matrix_tensor_dimension=16,ordinary_relation_rank=len(K),jordan_relation_rank=len(J),kernel_dimension=12,dual_relation_rank=len(KD),dual_kernel_dimension=2,jordan_left_ideal_falsifier=True,ordinary_flip_falsifier=True,scope='Known finite cases and route obstructions only; neither infinite-dimensional question resolved')
(L/'checks.json').write_text(json.dumps(r,indent=2)+'\n');print(r)

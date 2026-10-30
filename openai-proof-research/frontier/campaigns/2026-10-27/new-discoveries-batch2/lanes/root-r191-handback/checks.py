import itertools,json,math
from pathlib import Path
L=Path(__file__).resolve().parent

def compose(a,b):return tuple(b[a[i]] for i in range(len(a)))
def generated(S,identity):
 H={identity};todo=[identity]
 while todo:
  a=todo.pop()
  for b in S:
   c=compose(a,b)
   if c not in H:H.add(c);todo.append(c)
 return frozenset(H)
def subgroups(G,id):
 seen={frozenset([id])};todo=list(seen)
 while todo:
  H=todo.pop()
  for g in G:
   if g not in H:
    K=generated(list(H)+[g],id)
    if K not in seen:seen.add(K);todo.append(K)
 return list(seen)
def prime(n):return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
counts=[]
for n in [2,3,4]:
 G=list(itertools.permutations(range(n)));id=tuple(range(n));subs=subgroups(G,id);pairs=0
 orders={}
 for g in G:
  h=g;k=1
  while h!=id:h=compose(h,g);k+=1
  orders[g]=k
 for Y in subs:
  for Z in subs:
   if len(Y)!=len(Z):continue
   cosets=[]
   for H in [Y,Z]:
    C={frozenset(compose(h,g) for h in H) for g in G};cosets.append(list(C))
   A,B=cosets;edges={(i,j) for i,a in enumerate(A) for j,b in enumerate(B) if a&b}
   d=len(Y)//len(Y&Z)
   assert all(sum(i==x for i,j in edges)==d for x in range(len(A)))
   assert all(sum(j==x for i,j in edges)==d for x in range(len(B)))
   todo=[(0,0)];reach=set(todo)
   while todo:
    side,x=todo.pop();N=[(1,j) for i,j in edges if i==x] if side==0 else [(0,i) for i,j in edges if j==x]
    for v in N:
     if v not in reach:reach.add(v);todo.append(v)
   assert (len(reach)==len(A)+len(B))==(len(generated(Y|Z,id))==len(G))
   for g in G:
    if not prime(orders[g]):continue
    fixes=[any(frozenset(compose(h,g) for h in c)==c for c in C) for C in cosets]
    # Direct action fixed-coset condition, independently via conjugation.
    inv=tuple(g.index(i) for i in range(n))
    covered=[]
    for H in [Y,Z]:
     yes=False
     for x in G:
      xi=tuple(x.index(i) for i in range(n))
      if compose(compose(x,g),xi) in H:yes=True
     covered.append(yes)
    assert fixes==covered
   pairs+=1
 counts.append(dict(degree=n,group_order=len(G),subgroups=len(subs),equal_order_pairs=pairs))
# All labeled base graphs through order five: deck swap preserves every edge, is fixed-point-free.
lifts=0
for n in range(1,6):
 E=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(E)):
  e=[e for i,e in enumerate(E) if mask>>i&1]
  lifted={tuple(sorted((2*u,2*v+1))) for u,v in e}|{tuple(sorted((2*v,2*u+1))) for u,v in e}
  assert {tuple(sorted((u^1,v^1))) for u,v in lifted}==lifted
  assert all((i^1)!=i for i in range(2*n))
  lifts+=1
# A subgroup without semiregular elements does not control full Aut(K3).
S3=list(itertools.permutations(range(3)));swap=(1,0,2)
assert any(swap[i]==i for i in range(3))
assert all((1,2,0)[i]!=i for i in range(3))
result=dict(status='PASS',coset_controls=counts,double_cover_graphs=lifts,full_group_warning='K3: point-stabilizer C2 has no semiregular element, full S3 has a 3-cycle',limit='Finite diagnostics only; no source resolution or full-automorphism certificate for a semisymmetric counterexample.')
print(json.dumps(result,indent=2))

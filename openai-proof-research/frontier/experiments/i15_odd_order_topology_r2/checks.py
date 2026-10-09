#!/usr/bin/env python3
"""Independent finite diagnostics. No finite output is a topology proof."""
from pathlib import Path
from itertools import product
from collections import Counter
from fractions import Fraction as F
import json
OUT=Path(__file__).resolve().parent/'checks.json'
C=range(3); bad=[(a,b) for a in C for b in C if b!=(a+1)%3]
sets=[frozenset(a for a in C if mask>>a&1) for mask in range(1,8)]
trans=[]
for A,B in product(sets,repeat=2):
 # Check actual per-bundle integer allocations, independently of the logical implication.
 allowed=all(any((a not in A or n<=1) and (b not in B or 5-n<=1) for n in range(6)) for a,b in bad)
 if allowed: trans.append((tuple(sorted(A)),tuple(sorted(B))))
assert trans==[((0,),(1,)),((1,),(2,)),((2,),(0,))]
cycles={}
for d in range(2,11):
 count=sum(all((c[(i+1)%d]-c[i])%3==1 for i in range(d)) for c in product(C,repeat=d))
 assert count==(3 if d%3==0 else 0); cycles[d]=count
covers=[]
for d in range(2,61):
 incidence=[[] for _ in range(d)]; edges=[]
 for v in range(d):
  for a,b in bad:
   for q in range(5):
    eid=(v,a,b,q); w=(v+1)%d
    edges.append((eid,v,w,a,b)); incidence[v].append((eid,a)); incidence[w].append((eid,b))
 assert len(edges)==30*d and len({r[0] for r in edges})==len(edges)
 for inc in incidence:
  assert len(inc)==len({e for e,c in inc})==60
  assert Counter(c for e,c in inc)=={0:20,1:20,2:20}
 if d%3: continue
 received=[Counter() for _ in range(d)]; selected=Counter()
 for eid,v,w,a,b in edges:
  sv=a==v%3; sw=b==w%3
  assert not(sv and sw); selected[sv+sw]+=1
  endpoint=w if sv else v # choose initial if both unselected
  received[endpoint][b if endpoint==w else a]+=1
 assert selected=={0:10*d,1:20*d}
 assert all(r[v%3]==0 and not all(r[c]>=2 for c in C) for v,r in enumerate(received))
 covers.append(dict(d=d,edges=len(edges),zero_selected=selected[0],one_selected=selected[1]))
k=380**3*10**6*64; assert k==3511808000000000
# Recursive branch choice: retain only the path to the selected terminal leaf.
branch=(0,(1,2)); body=(branch,(3,(4,5)))
def leaves(t): return [t] if isinstance(t,int) else leaves(t[0])+leaves(t[1])
def count(t,i):
 if isinstance(t,int): assert t==i; return 1
 child=next(c for c in t if i in leaves(c)); return 2*count(child,i)
assert [count(branch,i) for i in range(3)]==[2,4,4]
# Euler characteristic of a tree of punctured tori: each has chi=-1, annular gluings chi=0.
assert 1-(-5)==6 and len(leaves(body))==6
# Magnus algebra, truncated beyond degree 7, independently derived with Xi=1+xi.
N=7
one={():1}
def add(a,b):
 c=Counter(a); c.update(b); return {w:v for w,v in c.items() if v}
def neg(a): return {w:-v for w,v in a.items()}
def mul(a,b):
 c=Counter()
 for u,x in a.items():
  for v,y in b.items():
   if len(u)+len(v)<=N: c[u+v]+=x*y
 return {w:v for w,v in c.items() if v}
def inv(a):
 assert a.get(())==1
 x=add(a,neg(one)); total=one; term=one
 for degree in range(1,N+1): term=mul(term,neg(x)); total=add(total,term)
 return total
def comm(a,b): return mul(mul(mul(a,b),inv(a)),inv(b))
def law(xs): return comm(comm(xs[0],comm(xs[1],xs[2])),comm(xs[3],comm(xs[4],xs[5])))
xs=[{():1,(i,):1} for i in range(6)]
plain=add(law(xs),neg(one)); assert min(map(len,plain))==6
assert len([w for w in plain if len(w)==6])==32
assert all(set(w)==set(range(6)) for w in plain)
for i in range(6):
 ys=xs.copy(); ys[i]=one; assert law(ys)==one
# Conjugations involving OTHER tips could be a genuine Brunnian failure if misplaced.
# Test tip and whole-subtree conjugations before testing independent external matrices.
ys=[mul(mul(xs[(i+2)%6],xs[i]),inv(xs[(i+2)%6])) for i in range(6)]
changed=add(law(ys),neg(one)); assert all(set(w)==set(range(6)) for w in changed)
assert {w:v for w,v in changed.items() if len(w)==6}=={w:v for w,v in plain.items() if len(w)==6}
# Exact matrix algebra in basis (e,h,f).
def mm(a,b): return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def sub(a,b): return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def bracket(a,b): return sub(mm(a,b),mm(b,a))
e=[[0,1],[0,0]]; h=[[1,0],[0,-1]]; f=[[0,0],[1,0]]
def tensor(u): return bracket(bracket(u[0],bracket(u[1],u[2])),bracket(u[3],bracket(u[4],u[5])))
assert tensor([e,h,f,h,h,e])==[[0,-16],[0,0]]
assert tensor([e]*6)==[[0,0],[0,0]] # a single unconjugated test cannot suffice
adj=[]
for a,b in product(range(3),repeat=2):
 g=[[1+a*b,a],[b,1]]; gi=[[1,-a],[-b,1+a*b]]
 cols=[]
 for x in [e,h,f]:
  z=mm(mm(g,x),gi); cols.append([z[0][1],z[0][0],z[1][0]])
 adj.append([[cols[j][i] for j in range(3)] for i in range(3)])
A=[[F(mat[i][j]) for mat in adj] for i in range(3) for j in range(3)]
def determinant(mat):
 a=[r[:] for r in mat]; det=F(1)
 for i in range(len(a)):
  j=next(j for j in range(i,len(a)) if a[j][i]);
  if i!=j: a[i],a[j]=a[j],a[i]; det=-det
  p=a[i][i]; det*=p
  for k in range(i+1,len(a)):
   q=a[k][i]/p
   for l in range(i,len(a)): a[k][l]-=q*a[i][l]
 return det
det=determinant(A); assert abs(det)==512
# Independent-block warning: after all six slots are identified, intersection (y) != product (y^6).
assert max([1]*6)==1 and sum([1]*6)==6
# Full square-zero algebra has squarefree mixed monomials, including all six plus parameters.
masks=range(1<<6)
nonzero_products=sum(not(a&b) for a,b in product(masks,repeat=2)); assert nonzero_products==3**6
assert (1|2)==3 and not(1&2) # t0*t1 survives
# Nonabelian kernel test for the height normal forms: phi(x)=xy, phi(y)=y.
def reduce(w):
 out=[]
 for a in w:
  if out and out[-1]==-a: out.pop()
  else: out.append(a)
 return tuple(out)
def word_inv(w): return tuple(-a for a in reversed(w))
def word_comm(a,b): return reduce(a+b+word_inv(a)+word_inv(b))
def word_law(xs): return word_comm(word_comm(xs[0],word_comm(xs[1],xs[2])),word_comm(xs[3],word_comm(xs[4],xs[5])))
free_word=word_law([(i,) for i in range(1,7)])
assert free_word
for i in range(1,7):
 assert not reduce(tuple(a for a in free_word if abs(a)!=i))
def power_y(n): return (2,)*n if n>=0 else (-2,)*(-n)
def phi(w,n):
 out=[]
 for a in w:
  out.extend((1,)+power_y(n) if a==1 else power_y(-n)+(-1,) if a==-1 else (a,))
 return reduce(out)
def gm(a,b):
 w,n=a; z,m=b; return reduce(w+phi(z,n)),n+m
words=[(),(1,),(2,),(-1,),(1,2,-1,-2)]
cases=0
for j,R in product([1,2],range(1,8)):
 s=3*R+j
 for u,v,a,b in product(words,words,range(-2,3),range(-2,3)):
  # New multiplication and its proposed image in the ORIGINAL extension.
  prod_new=(reduce(u+phi(v,s*a)),a+b)
  assert (prod_new[0],s*prod_new[1])==gm((u,s*a),(v,s*b)); cases+=1
assert phi((1,),3)!=(1,) # action genuinely nontrivial
result=dict(status='PASS: finite diagnostics only',deficiency_pairs=49,surviving_transitions=trans,cyclic_assignments=cycles,positive_covers=covers,body_count=k,terminal_sheet_counts=[2,4,4],surface_tree_handlebody_genus=6,exact_free_word_length=len(free_word),exact_free_word_deletions=6,magnus_max_degree=N,magnus_terms_by_degree=dict(Counter(map(len,plain))),conjugated_terms_by_degree=dict(Counter(map(len,changed))),tensor_value='-16e',adjoint_determinant_at_sigma_1=str(det),mixed_nilpotent_nonzero_products=nonzero_products,nonabelian_height_multiplication_cases=cases,invalid_shortcuts=['intersection=product after substitution','one unconjugated law','all parameters jointly square-zero','finite quotient implies exact outer order'],limitations='No topology, framings, all-degree theorem, PD duality, formal ideal inclusion, or manifold realization is certified by these finite tests.')
OUT.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps({k:v for k,v in result.items() if k!='positive_covers'},indent=2))

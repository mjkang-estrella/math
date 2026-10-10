#!/usr/bin/env python3
"""READ-ONLY finite diagnostics. No claim of proving CAT(0) geometry or source G."""
from fractions import Fraction as F
from itertools import product,permutations
import json

def reduce(w):
 out=[]
 for x in w:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return tuple(out)
def inv(w):return tuple(-x for x in w[::-1])
def comm(a,b):return reduce(a+b+inv(a)+inv(b))
def build(ws):
 n=len(ws);m=1<<(n-1).bit_length();cur=ws+[ws[-1]]*(m-n);calls=0
 while len(cur)>1:
  nxt=[]
  for a,b in zip(cur[::2],cur[1::2]):
   for s in [(),(1,),(2,)]:
    calls+=1;c=comm(a,reduce(s+b+inv(s)))
    if c:break
   else:raise AssertionError('three conjugators fail')
   nxt.append(c)
  cur=nxt
 assert cur[0] and len(cur[0])<=F(16*m*m-4,3) and calls<=3*(m-1)
 return cur[0],m,calls
P=list(permutations(range(3)))
def mul(a,b):return tuple(a[b[i]] for i in range(3))
def pinv(a):return tuple(a.index(i) for i in range(3))
def ev(w,a,b):
 q=(0,1,2);letters={1:a,2:b,-1:pinv(a),-2:pinv(b)}
 for x in w:q=mul(q,letters[x])
 return q
stats={}
n=0
for bm in [F(0),F(1,1000),F(1,7),F(3)]:
 a=F(1)
 for j in range(2,101):
  a=F((j-1)**2,j*j)*a+F(1,j*j)+2*bm*F(j-1,j*j)
  assert a==F(1,j)+bm*F(j-1,j);n+=1
stats['mean_recurrences']=n
n=0
for tau in [F(1,j) for j in range(2,66)]:
 B=12;M=6;t=(16*B*B*tau.denominator**2+tau.numerator**2-1)//tau.numerator**2
 b=tau*tau/(16*B*B*M);eta=min(tau*tau/(32*B*B*M*M),tau/(8*B*M))
 assert F(1,t)+b*M+2*M*M*eta<=3*tau*tau/(16*B*B)
 assert 2*B*M*eta<=tau/4;n+=1
stats['conditional_budgets']=n
n=0
for a,tau in product([F(j,1000) for j in range(31)],repeat=2):
 dlo=2-2*a-2*tau;du=4+4*a-dlo
 assert du==2+6*a+2*tau
 assert (4+4*a-2*dlo)/4==2*a+tau
 hs=2*(1+a)+2*du;opp=3-3*a-4*tau
 assert hs-opp==3+17*a+8*tau
 assert (hs-2*opp)/4==5*a+3*tau;n+=1
stats['square_hexagon_budgets']=n
# 2sqrt(2)<3, sqrt(2/3)<5/6, hence ratio<18; purely rational certificates.
assert F(8)<F(9) and F(2,3)<F(25,36)
assert F(275,9)<36
stats['separator_and_displacement_assertions']=3
leaves=[(1,),(2,),(1,1),(2,2),(1,2),(1,-2),(-1,2),(1,2,-1,-2),(-1,-2,1,2)]
count=images=kill=0;maxlen=0
for offset in range(len(leaves)):
 for m in range(1,33):
  ws=[leaves[(offset+i)%len(leaves)] for i in range(m)]
  w,M,calls=build(ws);count+=1;maxlen=max(maxlen,len(w))
  for a,b in product(P,repeat=2):
   images+=1
   if any(ev(q,a,b)==(0,1,2) for q in ws):
    assert ev(w,a,b)==(0,1,2);kill+=1
stats.update(free_group_lists=count,S3_maps=images,S3_kernel_implications=kill,max_test_word_length=maxlen)
for k in range(1,13):
 m=2**k;L=4
 for j in range(k):L=4*L+4
 assert L==F(16*m*m-4,3)
stats['balanced_length_recurrences']=12
n=0
for j in range(2,66):
 eps=F(1,j);assert 2-2*eps>0
 t=eps/2;d=2*max(t-eps,0);assert d==0
 t=F(1);d=2*max(t-eps,0);assert d==2-2*eps;n+=1
stats['actual_tree_distance_cases']=n
assert 32+2*90==212 and 7+1+90==98
stats['template_counts']=2
print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_ONLY','checks':stats},sort_keys=True,indent=2))

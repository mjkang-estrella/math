import itertools,json,math
from pathlib import Path
P=Path(__file__).resolve().parent
N=80
C=[[1]*(N+1) for _ in range(N+1)]
A=[[]]
for n in range(1,N+1):
 for l in range(n):C[n][l]=sum(math.comb(n-1,k)*min(l+1,k+1)*C[k][l]*C[n-1-k][l] for k in range(n))
 for l in range(n,N+1):C[n][l]=C[n][n-1]
 A.append([C[n][l]-(C[n][l-1] if l else 0) for l in range(n)])
a,b,c=A[80][39:42];x,y=A[62][30:32];u,v=A[61][30:32]
assert a*c>b*b and x*v>y*u

def std(w):
 order=sorted(range(len(w)),key=lambda i:(w[i],i));r=[0]*len(w)
 for rank,i in enumerate(order,1):r[i]=rank
 return tuple(r)
def foata(w):
 out=[]
 for x in w:
  if out:
   low=out[-1]<=x;blocks=[];block=[]
   for y in out:
    block.append(y)
    if (y<=x)==low:blocks.extend([y]+block[:-1]);block=[]
   assert not block
   out=blocks
  out.append(x)
 return tuple(out)
checks=0
for n in range(8):
 for w in itertools.product(range(1,4),repeat=n):
  assert std(foata(w))==foata(std(w));checks+=1
# a generic weighted sum of actual permutation-fiber pmfs need not be unimodal
inc=[1,7,10,6];dec=[1,0,0,0];mix=[a+20*b for a,b in zip(inc,dec)]
assert mix==[21,7,10,6]
# EGF Riccati coefficient identity, n<=25, l<=8; exact factorial-scaled coefficients
ode=0
for l in range(9):
 for n in range(26):
  rhs=(l+1)*sum(math.comb(n,k)*C[k][l]*C[n-k][l] for k in range(n+1))
  rhs-=sum(math.comb(n,k)*(l-k)*(1 if k==0 else (k+1)**(k-1))*C[n-k][l] for k in range(min(l,n+1)))
  assert rhs==C[n+1][l];ode+=1
out={'logconcavity_obstruction':{'n':80,'l':40,'a39':a,'a40':b,'a41':c,'a39_a41_minus_a40sq':a*c-b*b},
'likelihood_ratio_obstruction':{'n':62,'l':30,'cross_difference':x*v-y*u},
'standardization_foata_word_checks':checks,'riccati_coefficient_checks':ode,'weighted_fiber_mixture':mix}
(P/'route-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

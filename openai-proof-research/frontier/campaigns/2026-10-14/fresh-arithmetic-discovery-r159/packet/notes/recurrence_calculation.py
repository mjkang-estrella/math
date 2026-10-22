from pathlib import Path
from itertools import permutations
from fractions import Fraction
import json
ROOT=Path("frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r159")
def add(a,b):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a): c[i]+=v
 for i,v in enumerate(b): c[i]+=v
 while len(c)>1 and c[-1]==0: c.pop()
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b): c[i+j]+=u*v
 return add(c,[0])
def det(a):
 n=len(a); total=[0]
 for p in permutations(range(n)):
  sign=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)); term=[sign]
  for i in range(n): term=mul(term,a[i][p[i]])
  total=add(total,term)
 return total
def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def mm(a,b): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def sample(s):
 b=len(s); L=b+1
 def M(j): return [[int(d<=s[(j-d)%b]) for d in range(1,L+1)]]+[[int(c==i-1) for c in range(L)] for i in range(1,L)]
 A=eye(L)
 for j in range(1,b+1): A=mm(M(j),A)
 coeff=[1]
 for j in range(1,36): coeff.append(sum(coeff[j-d] for d in range(1,min(L,j)+1) if d<=s[(j-d)%b]))
 v=[[1]]+[[0] for _ in range(L-1)]
 for j in range(1,36):
  v=mm(M(j),v); assert v[0][0]==coeff[j]
 assert all(coeff[j]>=coeff[j-1] and coeff[j]<=2**j for j in range(1,len(coeff)))
 Z=[[[int(i==j),-A[i][j]] for j in range(L)] for i in range(L)]; den=det(Z)
 char=det([[[-A[i][j],int(i==j)] for j in range(L)] for i in range(L)])
 nums=[]
 for k in range(L):
  B=[[list(Z[i][j]) if j!=k else [int(i==0)] for j in range(L)] for i in range(L)]
  nums.append(det(B))
 B=eye(L); funcs=[]
 for phase in range(b):
  if phase: B=mm(M(phase),B)
  num=[0]
  for k in range(L): num=add(num,mul([B[0][k]],nums[k]))
  expansion=[]
  for m in range(12):
   val=Fraction(num[m] if m<len(num) else 0)
   val-=sum(den[d]*expansion[m-d] for d in range(1,min(len(den)-1,m)+1))
   expansion.append(val/den[0])
  assert all(expansion[m]==coeff[m*b+phase] for m in range(12))
  funcs.append({"numerator_low_to_high":num,"denominator_low_to_high":den})
 q=[0]*(len(coeff)+L)
 for j,a in enumerate(coeff):
  q[j]+=a
  for d in range(1,s[j%b]+1): q[j+d]-=a
 assert q[0]==1 and all(v==0 for v in q[1:len(coeff)])
 return {"word":s,"period_matrix":A,"characteristic_polynomial_low_to_high":char,"phase_generating_functions":funcs,"coefficients_first_24":coeff[:24],"terminal_class_residual":q[len(coeff):],"observation":"finite exact arithmetic; not a mathematical gate or a new case table"}
rows=[sample(s) for s in [[1],[2],[2,1],[3,1],[2,2]]]
(ROOT/"packet/notes/calculation-values.json").write_text(json.dumps(rows,indent=2)+"\n")
print(json.dumps(rows,indent=2))

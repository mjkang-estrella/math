import math,json,pathlib
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(7,24,2):
 dh=(n-1)*(n-2)//2;dd=n*(n-3)//2;coeff=[]
 for k in range(2,n+1):
  m=n-k;m2=int(k==2);ch=((m-1)**2-(m+2*m2-1))//2;cd=m*(m-1)//2+m2-m;sg=(-1)**(k-1);w=math.factorial(n)//(k*math.factorial(n-k));coeff.append([F(sg*ch*w,dh),F(sg*w),F(ch*w,dh),F(sg*cd*w,dd)])
 base=[coeff[-1][j]+coeff[-2][j] for j in range(4)];vals=base.copy();bad=[];mindiff=None
 prev=0
 for t in range(1<<(n-3)):
  mask=t^(t>>1)
  if t:
   change=mask^prev;k=change.bit_length()-1;sg=1 if mask>>k&1 else -1
   vals=[vals[j]+sg*coeff[k][j] for j in range(4)]
  prev=mask;gap=max(vals[1:])-vals[0];mindiff=gap if mindiff is None else min(mindiff,gap)
  if gap<=0:
   bad.append(mask)
   if n==23:break
 out.append({'n':n,'I_subsets':1<<(n-3),'bad':bad,'minimum_gap':str(mindiff),'completed_masks':t+1,'exhaustive':t+1==(1<<(n-3))})
(D/'outputs/characters.json').write_text(json.dumps(out,indent=2));print(out)

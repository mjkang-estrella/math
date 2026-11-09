import math,itertools,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1]
def pathcoef(m):
 l=sum(m.values());ones=m.get(1,0)
 if ones>1:return 0
 if not l:return 1
 w=math.prod((i-1)**v for i,v in m.items() if i>1);den=math.prod(math.factorial(v) for v in m.values())
 if ones:return math.factorial(l-1)*w//den
 val=math.factorial(l)*w//den
 for i,v in m.items():val+=math.factorial(l-1)*v*(w//(i-1))//den
 return val
# Avoid premature integer division in sum of terms by using exact common factorial ratio.
from fractions import Fraction as F
def pathcoef(m):
 l=sum(m.values());ones=m.get(1,0)
 if ones>1:return 0
 if not l:return 1
 w=math.prod((i-1)**v for i,v in m.items() if i>1);den=math.prod(math.factorial(v) for v in m.values())
 if ones:return math.factorial(l-1)*w//den
 val=F(math.factorial(l)*w,den)*(1+sum(F(v,i-1) for i,v in m.items())/l)
 assert val.denominator==1
 return val.numerator
def coeff(m,b):
 ans=pathcoef(m)
 if m.get(1,0):mm=m.copy();mm[1]-=1;mm={i:v for i,v in mm.items() if v};ans+=pathcoef(mm)
 items=list(m.items())
 for vv in itertools.product(*(range(min(v,(b+1)//i)+1) for i,v in items)):
  if sum(i*x for (i,v),x in zip(items,vv))!=b+1:continue
  left={i:x for (i,v),x in zip(items,vv) if x};right={i:v-x for (i,v),x in zip(items,vv) if v>x};ans-=pathcoef(left)*pathcoef(right)
 return ans
rows=[];bad=[]
for b in [4,6,10,12,16,18,22,24,28,30]:
 N=b*b+2*b+2;count=0;low=None;arg=None
 for i in range(1,17):
  for j in range(i+1,25):
   for t in range(N//j+1):
    rem=N-t*j
    if rem%i:continue
    m={i:rem//i,j:t};m={z:v for z,v in m.items() if v};v=coeff(m,b);count+=1
    if low is None or v<low:low=v;arg=m
    if v<0:bad.append({'b':b,'partition':m,'coefficient':v});print('FAIL',bad[-1],flush=True)
 row={'b':b,'N':N,'part_support':'at most two sizes i<j with 1<=i<=16, i<j<=24','tested_with_duplicates':count,'minimum':low,'argmin':arg};rows.append(row);print(row,flush=True)
(D/'outputs/spiders.json').write_text(json.dumps({'rows':rows,'failures':bad},indent=2))

from fractions import Fraction as F
import sys
sys.path.append('/home/mj-kang/.local/lib/python3.14/site-packages')
import numpy as np,json,pathlib,math
D=pathlib.Path(__file__).resolve().parents[1]
def rfi(N,r):
 a=[0]*r;a[-1]=int(N+1)+1 if r%2 else 2;s=1-(N+1)/a[-1] if r%2 else -N/a[-1]
 for j in range(r-2,-1,-1):
  if j%2==0:
   a[j]=int((N+1)/(1-1/s))+1;y=1-(N+1)/a[j];s=(s*y-1)/(s+y-2)
  else:
   a[j]=int(N/s)+1;y=-N/a[j];s=s*y/(s+y)
 return a
def mineig(a):
 r=len(a);M=np.zeros((r,r))
 for i in range(r):
  if i%2==0:M[i,i]=a[i]-1
  for j in range(i+1,r):
   if i%2==0:M[i,j]=M[j,i]=math.sqrt(a[i]*a[j])
 eig=np.linalg.eigvalsh(M);return min(e for e in eig if e>1e-7)
rows=[];bad=[]
for den in [7,10,13,31]:
 for num in range(1,12*den):
  N=F(num,den)
  for r in range(2,17):
   a=rfi(N,r)
   if max(a)>10000000:continue
   base=mineig(a);count=0;best=-1e99;wi=None
   for j,v in enumerate(a):
    if v<=(2 if j==r-1 else 1):continue
    b=a.copy();b[j]-=1;m=mineig(b);count+=1
    if m>best:best=m;wi=j
    if m>float(N)+1e-7:bad.append({'N':str(N),'a':a,'b':b,'minpos':m});print('FAIL',bad[-1],flush=True)
   rows.append({'N':str(N),'r':r,'a':a,'minpos':base,'decrements':count,'best_decrement':best if count else None,'coordinate':wi})
print('instances',len(rows),'decrements',sum(x['decrements'] for x in rows),'failures',len(bad))
(D/'outputs/threshold.json').write_text(json.dumps({'rows':rows,'failures':bad},indent=2))

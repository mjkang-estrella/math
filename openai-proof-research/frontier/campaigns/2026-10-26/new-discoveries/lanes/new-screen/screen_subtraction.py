import sys,random,json,itertools,time
sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/polynomial/.pydeps')
from flint import fmpz_poly
random.seed(45113);count=0;start=time.time()
for D in range(3,38,2):
 for mask in range(1,1<<((D-1)//2)):
  exps=[2*(i+1) for i in range((D-1)//2) if mask>>i&1];t=len(exps)+1
  a=[0]*(D+1);a[0]=1;a[D]=t
  for i in exps:a[i]=1
  p=fmpz_poly(a);g=p.gcd(p.derivative());count+=1
  if g.degree()>0:
   print('VIOLATION',D,exps,str(g));json.dump({'D':D,'exps':exps,'gcd':str(g)},open('subtraction-violation.json','w'));raise SystemExit
 print(D,count,time.time()-start,flush=True)
print('PASS exhaustive')
for i in range(100000):
 D=random.randrange(39,1000,2);t=random.randint(3,min(D//2,60));exps=random.sample(range(2,D,2),t-1)
 a=[0]*(D+1);a[0]=1;a[D]=t
 for j in exps:a[j]=1
 p=fmpz_poly(a);g=p.gcd(p.derivative())
 if g.degree()>0:print('VIOLATION',D,exps,str(g));break
else:print('PASS random')

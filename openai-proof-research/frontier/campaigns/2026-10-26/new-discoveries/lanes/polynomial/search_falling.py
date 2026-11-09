from pathlib import Path
import sys,math,time,json,argparse
sys.path.insert(0,str(Path(__file__).parent/'.pydeps'))
from flint import fmpz_poly
x=fmpz_poly([0,1]);one=fmpz_poly([1])
p=argparse.ArgumentParser();p.add_argument('A',type=int);p.add_argument('K',type=int);args=p.parse_args()
fall=[one]
for k in range(1,args.K+1):fall.append(fall[-1]*(x-(k-1)))
def known(k,a):
 if (k,a) in [(3,6),(4,7)]:return True
 for t in range(2,9):
  f=math.factorial(t)
  if (a,k)==(f-1,f-t):return True
 return False
start=time.monotonic();count=0;reducible=[]
for a in range(5,args.A+1):
 for k in range(2,min(args.K,a-3)+1):
  P=fall[k]-math.factorial(a)
  content,fac=P.factor();count+=1
  if len(fac)>1 or any(e>1 for _,e in fac):
   r={'k':k,'a':a,'known_exception':known(k,a),'factors':[(str(f),e) for f,e in fac]}
   reducible.append(r);print(json.dumps(r),flush=True)
   if not r['known_exception']:
    Path(__file__).with_name('falling-new-candidate.json').write_text(json.dumps(r,indent=2)+'\n')
    raise SystemExit()
 if a%10==0:print(json.dumps({'a_checked':a,'K':args.K,'cases':count,'seconds':round(time.monotonic()-start,2)}),flush=True)
Path(__file__).with_name('falling-result.json').write_text(json.dumps({'A':args.A,'K':args.K,'cases':count,'reducible':reducible},indent=2)+'\n')

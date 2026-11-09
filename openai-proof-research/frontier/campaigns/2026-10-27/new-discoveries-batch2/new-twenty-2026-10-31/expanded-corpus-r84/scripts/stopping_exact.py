import math,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];t=time.time();out=[]
for a,den in [(47,100),(48,100),(49,100),(495,1000),(499,1000)]:
 b=den-a;N=160;v=[1,1]+[0]*(N+2);U=1;cat=1;rows=[]
 for k in range(1,N+1):
  U*=den
  if k%2==0:
   j=k//2
   if j>1:cat=cat*(4*j-2)//(j+1)
   U-=cat*a**(j+1)*b**(j-1)
  cont=[a*v[max(j-1,0)]+b*v[j+1]for j in range(len(v)-1)]
  rows.append({'n':k,'stop_minus_continue_numerator':str(U-cont[1]),'denominator_power':k,'stop':U>=cont[1]})
  v=cont;v[:2]=[max(x,U)for x in v[:2]]
 out.append({'a':a,'denominator':den,'rows':rows,'even_violations':[k+2 for k in range(4,N-1,2)if rows[k-1]['stop'] and not rows[k+1]['stop']]})
(D/'outputs/stopping-exact.json').write_text(json.dumps({'scope':'All horizons 1..160 at 5 rational biases; exact integer-scaled Bellman arithmetic; no logs or floating point','cases':out,'wall_seconds':time.time()-t},indent=2)+'\n');print([(a['a'],a['denominator'],a['even_violations'])for a in out])

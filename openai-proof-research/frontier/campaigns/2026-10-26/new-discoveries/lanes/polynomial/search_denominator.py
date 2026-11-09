from pathlib import Path
import sys,json,time
sys.path.insert(0,str(Path(__file__).parent/'.pydeps'))
from flint import fmpz_poly
x=fmpz_poly([0,1]);d=fmpz_poly([1]);start=time.monotonic();bad=[]
N=int(sys.argv[1])
for n in range(1,N+1):
 v=(n&-n).bit_length()-1;odd=n>>v
 for i in range(v+1):d*=x**((2**i)*odd)+1
 c=list(map(int,d.coeffs()))
 failures=[j for j in range(1,(len(c)+1)//2) if c[j]**2<c[j-1]*c[j+1]]
 if failures:
  e={'n':n,'j':failures,'known':n in [3,5,6,7]};bad.append(e);print(json.dumps(e),flush=True)
  if not e['known']:
   Path(__file__).with_name('den-new-candidate.json').write_text(json.dumps(e,indent=2)+'\n');break
 if n%25==0:print(json.dumps({'den_checked':n,'degree':d.degree(),'seconds':round(time.monotonic()-start,2)}),flush=True)
Path(__file__).with_name('den-result.json').write_text(json.dumps({'N':N,'bad':bad},indent=2)+'\n')

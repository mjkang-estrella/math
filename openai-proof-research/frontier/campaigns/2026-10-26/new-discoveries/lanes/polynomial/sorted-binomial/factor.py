import sys,math,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'.pydeps'))
from flint import fmpz_poly
N=int(sys.argv[1]); start=time.time()
for n in range(2,N+1,2):
 p=fmpz_poly([math.comb(n,j//2) for j in range(n+1)])
 unit,fac=p.factor(); print(json.dumps({'n':n,'factors':[(f.degree(),e) for f,e in fac],'reducible':len(fac)>1 or fac[0][1]>1,'seconds':time.time()-start}),flush=True)

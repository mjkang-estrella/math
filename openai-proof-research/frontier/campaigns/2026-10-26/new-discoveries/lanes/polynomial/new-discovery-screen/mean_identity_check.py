from pathlib import Path
import sys,random,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'.pydeps'))
from flint import fmpq_poly,fmpq
from math import comb,factorial
rng=random.Random(336466)

def root_mean_eval(f,g):
    # Trace of multiplication by f in Q[X]/(g); handles all root multiplicities.
    n=g.degree(); trace=fmpq(0)
    for i in range(n):
        trace+=((f*fmpq_poly([0]*i+[1]))%g)[i]
    return trace/n
rows=[]
for D in range(1,36,2):
    for t in range(10):
        f=fmpq_poly([rng.randint(-9,9) for _ in range(D)]+[rng.choice([-3,-1,1,2])])
        g=f; ans=fmpq(0)
        for rho in range(1,D):
            g=g.derivative(); ans+=(-1)**rho*comb(D,rho)*root_mean_eval(f,g)
        assert ans==0,(D,f,ans)
    rows.append({'D':D,'random_polynomials':10,'method':'quotient-algebra multiplication trace','identity':True})
print(json.dumps(rows,indent=2))

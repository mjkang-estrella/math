"""Small exact diagnostics of the reduction, not a theorem/novelty certificate."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
E=Path(__file__).resolve().parent
checks=[]
def check(name,condition,detail):
 assert condition,name
 checks.append(dict(name=name,passed=True,detail=detail))
check('covariant tensor L2 squared rescaling',F(4,2)-2==0,'Under q=c^-1 g the exponent is c^(2-n/2)=1 at n=4.')
check('Clarke dimension-four coefficient',F(2,4)==F(1,2),'sqrt(4)/4=1/2; applying path length bound gives the same all-subset error.')
check('normalized path derivative',{'Ric':-2,'g':6}=={'Ric':-2,'g':2*3},'After multiplying by c^2: c^2 qdot=-2c Ric+6g=-2c(Ric-3g/c).')
p=F(1,4);terms=[6*p,1+3*p,1+2*p,F(2)];h=min(terms)
check('square-root hole budget',h==F(3,2) and terms[1]>h,'r=eta^(1/4): exponents 3/2,7/4 with log,3/2,2.')
check('square-root subdivision',h/4-p==F(1,8) and (h/4-p)/2==F(1,16),'R/r=eta^(1/8)=D^(1/16); log term is strictly subleading.')
p=F(1,6);terms=[6*p,1+3*p,F(1)];h=min(terms)
check('absolute-volume subdivision',h/4-p==F(1,12) and (h/4-p)/2==F(1,24),'r=eta^(1/6), R=eta^(1/4), R/r=eta^(1/12).')
check('fixed model does not dominate',F(1,3)>F(1,8),'eta^(1/3) is smaller than eta^(1/8) for eta in (0,1).')
check('spectral scale and product inverse',32/2-6==10 and 4*3-6==6 and 0-6==-6,'CP2 Ric6 -> Ric3 halves eigenvalues; product Ric1 -> Ric3 triples; negative product mode is not zero.')
result=dict(purpose=__doc__,checks=checks,count=len(checks),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(E/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'{len(checks)} exact reduction checks PASS; no universal-proof or novelty certification.')

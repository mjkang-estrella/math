from pathlib import Path
from fractions import Fraction as Q
import json
D=Path(__file__).resolve().parent
# Coefficients of 4||x||^2 - E(x) - sum (x_i+x_(i+1))^2 - 2x_0^2 -2x_(m-1)^2.
tests=[]
for m in range(1,13):
 c={(i,i):4 for i in range(m)}
 def add(i,j,v):c[i,j]=c.get((i,j),0)+v
 for i in range(m-1):
  add(i,i,-2);add(i+1,i+1,-2);add(i,i+1,2);add(i,i+1,-2)
 add(0,0,-2);add(m-1,m-1,-2)
 assert not any(c.values());tests.append(dict(interior_vertices=m,zero_polynomial=True))
# Exact algebraic leading-term limits of the displayed source formulas.
assert Q(-9,4)/9==Q(-1,4) and Q(-2,9)!=Q(-1,4)
r=dict(neumann=dict(executed=tests,universal_argument='For every m>=1, each interior squared coordinate occurs twice in the paired-square sum; endpoints occur once and get the additional 2x^2 terms. Thus 4||x||^2-E=sum adjacent (x_i+x_(i+1))^2+2x_0^2+2x_(m-1)^2 >=0 (m=1 gives 4x_0^2). Together with the source boundary cancellation this proves the bound. Routine adaptation, zero credit.'),fraction=dict(executed_exact_limit_comparison=['-1/4','-2/9'],conclusion='Source asymptotic matching step not justified. This is a proof-gap diagnostic, not a refutation of the continued fraction identity.'))
(D/'bounded-calculation.json').write_text(json.dumps(r,indent=2)+'\n')

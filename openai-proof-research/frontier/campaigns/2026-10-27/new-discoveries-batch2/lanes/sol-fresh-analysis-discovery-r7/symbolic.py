import os
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
import resource
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
import sympy as s,json
from pathlib import Path
b,t=s.symbols('b t');rows=[]
def R(n):return sum(n/(n*n-b*k*n+k*k) for k in range(1,n+1))
for n in range(1,13):
 d=s.cancel(R(n)-R(n+1));num,den=s.fraction(d)
 # orient denominator positive in b<2
 if den.subs(b,1)<0:num=-num;den=-den
 # coefficient cone b=3/2+t/(1+t) /2 covers [1.5,2)
 deg=s.degree(num,b)
 pol=s.Poly(s.expand(sum(coef*(3+4*t)**i*(2*(1+t))**(deg-i) for (i,),coef in s.Poly(num,b).terms())),t)
 co=pol.all_coeffs()
 rows.append({'n':n,'degree':int(deg),'positive_Bernstein_on_1.5_2':all(c>=0 for c in co),'negative_coeff_indices':[i for i,c in enumerate(reversed(co)) if c<0]})
 print(rows[-1],flush=True)
Path(__file__).with_name('symbolic-checks.json').write_text(json.dumps(rows,indent=2))

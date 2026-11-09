from pathlib import Path
import sys,json,math,hashlib
from fractions import Fraction as F
sys.set_int_max_str_digits(0)
sys.path.insert(0,str(Path(__file__).resolve().parent))
from rootcount_scan import polys
from flint import fmpq
k=48;lo=F(61,1000);hi=F(613,10000)
assert lo*(1+lo)**(k-1)<1<hi*(1+hi)**(k-1)
row=[F(1,math.factorial(k-1))]+[F(0)]*(k+2)
for t in range(1,k+2):
 row=[F(0)]+[(k*j-t+1)*row[j]+k*row[j-1] for j in range(1,k+3)]

def eval_direct(x):
 y=x**k;sm=sum(x**i for i in range(k));p=y-1
 rr=sum((-1)**j*math.factorial(j)*row[j+2]*(p**(k-j-1)*y**(j+1)-p**k)for j in range(k))
 ss=sum((-1)**j*math.comb(k+1,j+2)*(x**(j+1)*(x-1)**(k-j-1)*sm**k-p**k)for j in range(k))
 return rr,ss
rp,sp=polys(k)
rows=[]
for x,sign in [(F(1,100),-1),(F(1,10),1),(F(1,2),-1),(F(3,5),1),(F(4,5),-1)]:
 r,s=eval_direct(x)
 rr=rp(fmpq(x.numerator,x.denominator));ss=sp(fmpq(x.numerator,x.denominator))
 assert F(int(rr.numerator),int(rr.denominator))==r
 assert F(int(ss.numerator),int(ss.denominator))==s
 vals=[lo*r-s,hi*r-s]
 assert all(v*sign>0 for v in vals)
 rows.append({'x':str(x),'sign':sign,'rho_negative':r<0,'sigma_over_rho':str(s/r),'lo_eval_numerator':str(vals[0].numerator),'lo_eval_denominator':str(vals[0].denominator),'hi_eval_numerator':str(vals[1].numerator),'hi_eval_denominator':str(vals[1].denominator)})
out={'mathdb_id':357503,'k':k,'degree':k*k-1,'alpha_interval':[str(lo),str(hi)],'alpha_defining_equation':'alpha*(1+alpha)^47=1, alpha>0','root_intervals':[['1/100','1/10'],['1/10','1/2'],['1/2','3/5'],['3/5','4/5']],'method':'exact source recurrence and rational evaluation; independent expanded FLINT polynomials agree','samples':rows}
p=Path(__file__).resolve().parent
(p/'rootcount-exact-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'k':k,'alpha_interval':[str(lo),str(hi)],'signs':[z['sign']for z in rows],'exact':True,'certificate_sha256':hashlib.sha256((p/'rootcount-exact-certificate.json').read_bytes()).hexdigest()},indent=2))

import os,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
from fractions import Fraction as F
from pathlib import Path
import json
# Independent scalar expansion of the gap-weighted recurrence; no iterate grid.
for k,d,b,c in [(F(1,2),F(1,6),F(7,15),F(6,5)),(F(1),F(1,4),F(4,5),F(2))]:
 S=2*k*(k-d);Sn=S-2*d*b+d*d*c
 dn=(k-d)-Sn/(2*(k-d))
 assert dn/d==(b-d*c/2)/(k-d)-1
# Exact secant-kernel test, f=1-x, g=(1-x)^2, x=t^2.
for t in [F(1,7),F(1,3),F(2,3),F(4,5)]:
 x=t*t
 Nf=(1-x)**2/2;Ng=F(1,3)-x+F(2,3)*t**3
 H=1-3*x+2*t**3
 B=(Nf-Ng)/F(1,6)
 p2=(B-H)/(F(1,2)*F(1,5))
 assert p2==30*x*(1-t)**2
# Gap density p1=6x(1-x); elementary polynomial integration.
p1=[F(0),F(6),F(-6)];h1h2=[F(2),F(-3),F(1)]
I=sum(a*b/F(i+j+1) for i,a in enumerate(p1) for j,b in enumerate(h1h2))
assert I/(2*F(1,3))-1==F(1,5)
# Endpoint limits p3/p2, from source derivative identity and h3 explicit.
k3=F(3,10);d2=F(1,30);d3=F(1,70)
left=(F(-3)+1/k3)*(d2/d3)
h3dd1=F(3,2);h4dd1=1/(k3*3)
right=(h3dd1-h4dd1)/F(1,2)*(d2/d3)
assert left==F(7,9) and right==F(49,27) and left<right
r={'status':'PASS','ordinary_proof':False,'credit':0,'secant_exact_samples':4,'gap_quotient_endpoint_limits':[str(left),str(right)],'limits':{'address_space_bytes':512*1024**2,'cpu_seconds':30,'blas_omp_threads':1}}
p=Path(__file__).with_name('checks.json');p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

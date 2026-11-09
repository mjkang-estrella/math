#!/usr/bin/env python3
import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
import sympy as s,json,random
from pathlib import Path
from check import shape,degree,encode,bal
x=s.Symbol('x');rng=random.Random(319089)
def poly(t):
 if t is None:return s.Poly(x,x)
 a,b=map(poly,t);return a*a+b*b*b
out=[];tested=0
for _ in range(350):
 t=shape(rng.randrange(3,15))
 if degree(t)>180:continue
 a,b=map(poly,t);d=a.degree();e=b.degree();g=s.gcd(a,b*b);h=g.degree();tested+=1
 if 2*e-h<=d-1 and d-h<=e-1:
  out.append(dict(shape=encode(t),A=str(a.as_expr()),B=str(b.as_expr()),gcd=str(g.as_expr()),d=d,e=e,h=h))
r=dict(tested=tested,degree_cap=180,failures=out)
Path(__file__).with_name('gcd-checks.json').write_text(json.dumps(r,indent=2));print(r)

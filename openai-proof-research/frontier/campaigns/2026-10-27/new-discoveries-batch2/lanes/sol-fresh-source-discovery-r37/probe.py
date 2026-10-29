import os,resource,signal,json,pathlib
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(55)
import sympy as s
x,y=s.symbols('x y')
def R(n,a,b):
 return s.Poly(s.expand(sum(s.rf(-n,k)*s.rf(n-a-b-1,k)*s.rf(-x,k)*s.rf(-y+k,n-k)/(s.rf(-a,k)*s.factorial(k)) for k in range(n+1))),x,y)
results=[]
for n in range(2,8):
 for a in range(n,n+4):
  for b in range(a,n+4):
   p=R(n,a,b); f=s.factor_list(p.as_expr());degs=sorted([s.Poly(q,x,y).total_degree() for q,e in f[1] for _ in range(e)])
   expected=[1,n-1] if a==b and n%2 else [n]
   results.append([n,a,b,degs])
   if degs!=sorted(expected):print('FALSIFIER',n,a,b,s.factor(p.as_expr()),flush=True)
print(json.dumps(results))
pathlib.Path(__file__).with_name('probe-results.json').write_text(json.dumps(results,indent=2))

import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import sympy as S,json,time,pathlib
x=S.Symbol('x');P=pathlib.Path(__file__).resolve().parent

def parts(n,lo=1):
 if n==0:yield ()
 for a in range(lo,n+1):
  for p in parts(n-a,a):yield (a,)+p
out=[]
for n in range(2,21):
 st=time.time();D=S.Poly(1,x)
 for d in range(1,n+1):D*=S.Poly(S.cyclotomic_poly(2*d,x),x)**(n//d)
 N=S.Poly(0,x)
 for p in parts(n):
  Q=S.Poly(1,x)
  for a in p:Q*=S.Poly(x**a+1,x)
  N+=D.exquo(Q)
 c,fs=S.factor_list(N);r={'n':n,'degree':N.degree(),'content':int(c),'factors':[(str(f.as_expr()),e) for f,e in fs],'seconds':time.time()-st};out.append(r)
 (P/'factor-checks.json').write_text(json.dumps(out,indent=2));print(n,N.degree(),[(f.degree(),e) for f,e in fs],flush=True)
 if len(fs)>1 or fs[0][1]>1:
  (P/'factor-witness.json').write_text(json.dumps({'n':n,'N':str(N.as_expr()),'D':str(D.as_expr()),'factorization':r},indent=2));break

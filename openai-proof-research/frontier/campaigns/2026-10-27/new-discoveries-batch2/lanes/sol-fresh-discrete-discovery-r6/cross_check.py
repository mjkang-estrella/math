import os,resource
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import sympy as S,json,pathlib
P=pathlib.Path(__file__).resolve().parent;x=S.Symbol('x');D=S.Poly(1,x);rows=[]
for n in range(1,51):
 b=n;L=2
 while b%2==0:b//=2;L*=2
 D*=S.Poly(sum(x**(j*b) for j in range(L)),x)
 C=S.Poly(1,x)
 for d in range(1,n+1):C*=S.Poly(S.cyclotomic_poly(2*d,x),x)**(n//d)
 assert C==D
 coeff=list(reversed(D.all_coeffs()));bad=[i for i in range(1,len(coeff)-1) if coeff[i]**2<coeff[i-1]*coeff[i+1]]
 assert bool(bad)==(n in [3,5,6,7])
 assert D.degree()==n*(n+1)-sum(j//(j&-j) for j in range(1,n+1))
 rows.append({'n':n,'degree':D.degree(),'bad_indices':bad,'palindromic':coeff==coeff[::-1]})
(P/'cross-checks.json').write_text(json.dumps(rows,indent=2));print('PASS: 50 independent cyclotomic/product comparisons, degrees and exact LC checks')

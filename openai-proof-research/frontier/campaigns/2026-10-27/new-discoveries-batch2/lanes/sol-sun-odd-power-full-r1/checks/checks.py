from pathlib import Path
import math,json,datetime
import sympy as S
pdir=Path(__file__).resolve().parents[1]
rows=[]
for p in list(S.primerange(3,44)):
 for h in range(5,p+2,2):
  for k in range(1,(p+1)//h+1):
   N=p-2*k; H=[0]
   for j in range(1,N+1):H.append((H[-1]+pow(j,-1,p))%p)
   harmonic=h*sum((-1)**r*pow(math.comb(N,r),h,p)*(H[N]-H[N-r]) for r in range(N+1))%p
   assert harmonic==0
   assert sum((-1)**r*math.comb(N,r)**h for r in range(N+1))==0
   vals=[];mod=p*p
   for u in range(p):
    x=N+p*u;b=1;value=0
    for r in range(p):
     if r:b=b*(x-r+1)*pow(r,-1,mod)%mod
     value=(value+(-1)**r*pow(b,h,mod))%mod
    assert value==0
   assert k<(p+(h-1)//2)/h
   rows.append(dict(p=p,h=h,k=k,harmonic=harmonic,all_p_lifts=True))
q=S.Symbol('q');pivot=[]
for n in [4,7,13,16]:
 M=S.Poly(S.cyclotomic_poly(n,q)**2,q,domain=S.QQ)
 term=S.Poly(1,q,domain=S.QQ);total=term
 for k in range(1,n):
  numerator=S.Poly(q**9*(1-q**(1+9*(k-1)))*(1-q**(2+9*(k-1)))*(1-q**(6+9*(k-1))),q,domain=S.QQ)
  denominator=S.Poly((1-q**(9*k))**3,q,domain=S.QQ)
  term=(term*numerator*S.invert(denominator,M)).rem(M)
  total=(total+term).rem(M)
 assert total.is_zero
 pivot.append(dict(n=n,exact_QQ_mod_cyclotomic_squared=True))
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sun_rows=rows,sun_parameter_triples=len(rows),sun_all_residue_lifts=sum(r['p'] for r in rows),pivot=pivot,limit='Finite exact checks only, not a universal proof or novelty evidence.')
(pdir/'checks/results.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='sun_rows'},indent=2))

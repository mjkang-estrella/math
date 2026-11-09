from fractions import Fraction
import json,pathlib,itertools
D=pathlib.Path(__file__).resolve().parents[1];rows=[];N=350
# Exact numerator subset expansion projected to integral exponents; denominator only integral exponents.
for k in range(1,19):
 p=[0]*(N+1);p[0]=1
 for j in range(1,k+1):
  for d in range(j,N+1):p[d]+=p[d-j]
 # product (1-q^(r+j)) for j=1..k: collect coefficient by cardinality and sum of j.
 polys=[{} for _ in range(k+1)];polys[0][0]=1
 for j in range(1,k+1):
  for s in range(j,0,-1):
   for e,c in list(polys[s-1].items()):polys[s][e+j]=polys[s].get(e+j,0)+c
 def coeff(r):
  ans=[0]*(N+1)
  for s in range(k+1):
   if (s*r).denominator!=1:continue
   for e,c in polys[s].items():
    shift=e+int(s*r)
    for d in range(shift,N+1):ans[d]+=(-1)**s*c*p[d-shift]
  return ans
 base=coeff(Fraction(1,2));num=0;bad=[]
 for r in sorted({Fraction(a,b) for b in range(1,14) for a in range(1,4*b+1)}):
  c=coeff(r);num+=1
  if any(x<y for x,y in zip(base,c)):
   d=next(i for i in range(N+1) if base[i]<c[i]);bad.append(dict(r=str(r),degree=d,half=base[d],other=c[d]))
 rows.append(dict(k=k,degree_cap=N,rationals=num,counterexamples=bad));print(rows[-1],flush=True)
 (D/'outputs/q.json').write_text(json.dumps(rows,indent=2)+'\n')

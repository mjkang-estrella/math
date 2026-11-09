from fractions import Fraction as F
import pathlib,json,math
P=pathlib.Path(__file__).resolve().parent
out={'status':'executed exact integer/rational arithmetic','purpose':'instances only; no uniform proof or novelty inference','riemann':[]}
def sums(b,n,right):return sum((1/(1-b*F(i,n)+F(i,n)**2) for i in range(1 if right else 0,n+1 if right else n)),F(0))/n
for b,right in [(F(3,4),False),(F(5,4),True),(F(7,4),False),(F(7,4),True)]:
 vals=[sums(b,n,right) for n in range(1,41)];diff=[v-u for u,v in zip(vals,vals[1:])];w={}
 for sign in [-1,1]:
  for n,d in enumerate(diff,1):
   if d*sign>0:w[str(sign)]={'n':n,'difference':str(d)};break
 out['riemann'].append({'b':str(b),'side':'right' if right else 'left','n_range':[1,40],'first_sign_witnesses':w})
def leg(a,p):return 0 if a%p==0 else (1 if pow(a%p,(p-1)//2,p)==1 else -1)
p=5;A=[[(j*j-k*k)**3*leg(j*j-k*k,p) for k in [1,2]] for j in [1,2]];D=A[0][0]*A[1][1]-A[0][1]*A[1][0];root=math.isqrt(D)
out['sun_p5']={'matrix':A,'D':D,'sqrt':root,'lhs':leg(root,p),'rhs':(-1)**sum(leg(k,p)==-1 for k in range(1,(p+3)//4))*leg(p,4+(-1)**((p-1)//4))}
assert root*root==D and out['sun_p5']['lhs']==out['sun_p5']['rhs']
(P/'calculations.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

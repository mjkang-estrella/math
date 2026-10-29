import json,pathlib
from fractions import Fraction as F
from routes import A,g,fac
P=pathlib.Path(__file__).resolve().parent
def val(a,x):
 r=F(0)
 for z in a[::-1]:r=r*x+z
 return r
rows=[]
for x in [F(1),F(3,2),F(5),F(6)]:
 p=[val(a,x)/f for a,f in zip(A,fac)]
 get=lambda k:p[k] if k>=0 else F(0)
 for n in range(1,21):
  positive=F(0);negative=F(0);negterms=[]
  for i in range(1,n+2):
   for j in range(i+1,n+2):
    det=get(n-i)*get(n+1-j)-get(n-j)*get(n+1-i)
    z=F((j-i)*g[i]*g[j],i*j)*det
    if z>=0:positive+=z
    else:negative+=z;negterms.append([i,j])
  dp=lambda k:val([i*z for i,z in enumerate(A[k])][1:],x)/fac[k]
  w=(n+1)*dp(n)*p[n+1]-n*p[n]*dp(n+1)
  assert w==x*(positive+negative)
  rows.append({'n':n,'x':str(x),'positive_sum':str(positive),'negative_sum':str(negative),'negative_pairs':negterms,'total_sign':int(w>0)-int(w<0)})
# Strict global submultiplicativity alone does not imply decreasing nth roots.
a=lambda n:3 if n==7 else 2
assert all(a(i)*a(j)>a(i+j) for i in range(1,20) for j in range(1,20))
assert a(6)**7<a(7)**6
(P/'kernel.json').write_text(json.dumps({'identity_checks':len(rows),'rows':rows,'submultiplicative_obstruction':{'a6':2,'a7':3,'all_positive_index_proof':'Each term is in [2,3], so every product is >=4>3.'}},indent=2))
print(json.dumps({'identity_checks':len(rows),'rows_with_negative_pairs':len([r for r in rows if r['negative_pairs']]),'negative_totals':[r for r in rows if r['total_sign']<0]}))

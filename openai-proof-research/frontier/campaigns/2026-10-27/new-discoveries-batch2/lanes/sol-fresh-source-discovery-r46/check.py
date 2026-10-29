import math,json,time,pathlib
from sympy import Poly,Symbol
P=pathlib.Path(__file__).resolve().parent;x=Symbol('x');start=time.monotonic(); rows=[]; moment_cases=0; recurrence_cases=0
for m in [5,6,7,8,9,10,12]:
 a=[[1]]
 for n in range(1,71):
  row=[0]*(n+1)
  for j in range(1,min(n,m)+1):
   w=math.comb(n-1,j-1)
   for k,v in enumerate(a[n-j]):row[k+1]+=w*v
  a.append(row); recurrence_cases+=1
  if n<10:continue
  moment_cases+=1
  lo=next(k for k,v in enumerate(row) if v); coeff=row[lo:];p=Poly.from_list(coeff[::-1],x)
  # Exact Hermite moment necessary conditions, including all 2x2 principal minors.
  d=p.degree();c=p.all_coeffs();s=[d]
  for k in range(1,2*d-1):
   v=-sum(c[j]*s[k-j] for j in range(1,min(k,d)+1) if j<k)
   if k<=d:v-=k*c[k]
   s.append(v)
  bad=next(((i,j,s[2*i]*s[2*j]-s[i+j]**2) for i in range(d) for j in range(i+1,d) if s[2*i]*s[2*j]-s[i+j]**2<0),None)
  if bad:
   r={'m':m,'n':n,'zero_multiplicity':lo,'coefficients_ascending':coeff,'hermite_negative_minor':[bad[0],bad[1],int(bad[2])],'elapsed':time.monotonic()-start};rows.append(r);print(json.dumps(r),flush=True);break
  if n<=30 and n%5==0:
   nr=int(p.count_roots(-math.inf,math.inf));rows.append({'m':m,'n':n,'degree':d,'real_distinct':nr});print(m,n,d,nr,flush=True)
(P/'checks.json').write_text(json.dumps({'rows':rows,'moment_cases':moment_cases,'recurrence_cases':recurrence_cases,'seconds':time.monotonic()-start},indent=2))

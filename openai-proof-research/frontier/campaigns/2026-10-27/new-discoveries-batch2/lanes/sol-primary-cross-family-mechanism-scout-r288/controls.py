from run import L, dump, save, sha
from fractions import Fraction as F
from math import comb, factorial
import urllib.request,time
def coeff(k,m,N):
 w=[F((-1)**j*comb(m,j)*factorial(k+m-j),factorial(k+m)) for j in range(m+1)]
 c=[F(1)]
 for n in range(1,N+1):c.append(-sum((w[j]*c[n-j] for j in range(1,min(m,n)+1)),F(0)))
 return w,c
rows=[]
for m in range(1,42,2):
 w,c=coeff(m,m,240)
 # Independent convolution recomputes every identity, rather than checking only signs.
 residual=[sum((w[j]*c[n-j] for j in range(min(m,n)+1)),F(0)) for n in range(241)]
 assert residual==[F(1)]+[F(0)]*240
 rows.append(dict(m=m,k=m,n_max=240,all_positive=all(v>0 for v in c),nonpositive=[i for i,v in enumerate(c) if v<=0]))
published=[]
for k,m,n in [(66,5,38),(44,7,37),(45,9,42)]:
 v=coeff(k,m,n)[1][-1];assert v<0
 published.append(dict(k=k,m=m,n=n,numerator=str(v.numerator),denominator=str(v.denominator)))
transforms=[]
for m in [3,5,7,9]:
 w,c=coeff(m,m,30)
 a=[sum((w[j]*F(1,2**(n-j)*factorial(n-j)) for j in range(min(m,n)+1)),F(0)) for n in range(13)]
 transforms.append(dict(m=m,q_times_exp_half=[str(v) for v in a],positive_after_constant=[i for i,v in enumerate(a) if i and v>0]))
dump(L/'checks/exact-controls.json',dict(diagonal=rows,published_negative_controls=published,transform=transforms,scope='finite exact tests only; no universal positivity conclusion'))
queries={'pade':'all:%22Fasi%22+AND+all:%22Higham%22','bessel':'all:%22Bessel+polynomials%22+AND+all:%22positivity%22'}
for name,q in queries.items():
 u='https://export.arxiv.org/api/query?search_query='+q+'&max_results=5&sortBy=submittedDate&sortOrder=descending'
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read(2000000);s=r.status
  p=L/'successor-search'/(name+'.xml');save(p,b);dump(p.with_suffix('.json'),dict(url=u,status=s,sha256=sha(p),retrieved=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())))
 except Exception as e:dump(L/'successor-search'/(name+'-failure.json'),dict(url=u,error=str(e)))
print('exact controls completed',len(rows),'diagonal parameters;',len(published),'published negative controls')

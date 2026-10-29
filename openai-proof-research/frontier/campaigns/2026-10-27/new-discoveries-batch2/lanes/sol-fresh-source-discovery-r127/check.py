import hashlib,json,math
from pathlib import Path
L=Path(__file__).resolve().parent
def factors(n):
 out=[];q=2
 while q*q<=n:
  if n%q==0:
   out.append(q);n//=q
   if n%q==0:return None
  q+=1
 if n>1:out.append(n)
 return out
rows=[]
for n in range(30,251,2):
 fs=factors(n)
 if fs is None or len(fs)<3:continue
 p=max(fs);d=n//p
 if d>=2*p:continue
 units={a for a in range(-n//2+1,n//2+1) if math.gcd(a,n)==1}
 best=0;w=None
 for h in range(1,n):
  lengths={}
  for a in sorted(units,reverse=True):
   v=1+lengths.get(a+h,0);lengths[a]=v
   if v>best:best=v;w=[a,h,v]
 k=(p*d-2*p)//d
 assert best==k
 y=-n//2+2*p
 assert all(y+i*d in units for i in range(1,k+1))
 rows.append(dict(n=n,p=p,d=d,maximum=best,witness=w))
def gauss(N,k):
 # Coefficient DP via subset sums, independent of the product division below.
 dp=[[1]]+[[] for _ in range(k)]
 for v in range(N):
  for j in range(min(k,v+1),0,-1):
   a=dp[j-1];b=dp[j]
   b.extend([0]*max(0,len(a)+v-len(b)))
   for i,x in enumerate(a):b[i+v]+=x
 shift=k*(k-1)//2
 return dp[k][shift:]
def div_qint(a,b):
 y=[x-(a[i-1] if i else 0) for i,x in enumerate(a)]+[-a[-1]]
 x=[]
 for i,v in enumerate(y):x.append(v+(x[i-b] if i>=b else 0))
 while x and x[-1]==0:x.pop()
 def mul_qint(z,b):
  r=[0]*(len(z)+b-1)
  for i,v in enumerate(z):
   for j in range(b):r[i+j]+=v
  return r
 assert mul_qint(x,b)==a
 return x
g=gauss(30,3);u=div_qint(g,7);p=div_qint(u,10)
assert len(u)-1==75 and len(p)-1==66
assert all(u[i]>=u[i-1] for i in range(2,75//2+1))
assert p[11]==-1 and 11 not in (1,65)
neg=[[i,v] for i,v in enumerate(p) if v<0]
assert neg==[[1,-1],[11,-1],[55,-1],[65,-1]]
bindings=0
for name in ['context-receipts.json','original-receipts.json']:
 for r in json.loads((L/name).read_text()):
  assert hashlib.sha256((L/r['copy']).read_bytes()).hexdigest()==r['sha256'];bindings+=1
for line in (L/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'copy' in r:
  assert hashlib.sha256((L/r['copy']).read_bytes()).hexdigest()==r['sha256'];bindings+=1
out=dict(status='PASS',residue_cases=rows,gaussian_public_witness=dict(N=30,k=3,a=7,b=10,degree_U=75,degree_P=66,negative_coefficients=neg),hash_bindings=bindings,scope='Finite reproduction of public results only; no source-resolution or novelty claim.')
(L/'check-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',residue_cases=len(rows),negative_coefficients=neg,hash_bindings=bindings)))

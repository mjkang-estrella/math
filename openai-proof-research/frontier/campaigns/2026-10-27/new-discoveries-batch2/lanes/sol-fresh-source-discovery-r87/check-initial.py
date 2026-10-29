import math,json,pathlib
from fractions import Fraction
p=pathlib.Path(__file__).parent

def factors(n):
 r={};d=2
 while d*d<=n:
  while n%d==0:r[d]=r.get(d,0)+1;n//=d
  d+=1
 if n>1:r[n]=1
 return r

def mu(n):
 f=factors(n);return 0 if any(v>1 for v in f.values()) else (-1)**len(f)
def phi(n):
 for d in factors(n):n=n//d*(d-1)
 return n
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def formula(i,j):
 a,b=factors(i),factors(j)
 if any(a[q]!=b[q] for q in a.keys()&b.keys()):return 0
 return (-1)**len(a.keys()&b.keys())*phi(math.lcm(i,j))
def rankmod(n,prime=1000003):
 a=[[(math.lcm(i,j)+math.gcd(i,j))%prime for j in range(1,n+1)] for i in range(1,n+1)];r=0
 for c in range(n):
  s=next((s for s in range(r,n) if a[s][c]),None)
  if s is None:continue
  a[r],a[s]=a[s],a[r];inv=pow(a[r][c],-1,prime);row=a[r]
  for k in range(c,n):row[k]=row[k]*inv%prime
  for s in range(r+1,n):
   t=a[s][c]
   if t:
    a[s][c]=0
    for k in range(c+1,n):a[s][k]=(a[s][k]-t*row[k])%prime
  r+=1
 return r
checks={};errors=[]
for i in range(1,49):
 for j in range(1,49):
  actual=sum(mu(i//d)*mu(j//e)*math.lcm(d,e) for d in divisors(i) for e in divisors(j))
  assert actual==formula(i,j),(i,j)
checks['mobius_congruence_pairs']=48**2
samples=list(range(4,65))+[95,96,127,128,191,192,255]
checks['ranks']=[{'n':n,'rank_mod_1000003':rankmod(n),'predicted_singular':bin(n).startswith('0b10')} for n in samples]
for v in checks['ranks']:
 assert (v['rank_mod_1000003']<v['n'])==v['predicted_singular'],v
checks['known_vector']=[{'s':s,'endpoint':3*2**(s+1),'last_residual':2*(math.lcm(2**s,3*2**(s+1))+math.gcd(2**s,3*2**(s+1)))-3*(math.lcm(2**(s+1),3*2**(s+1))+math.gcd(2**(s+1),3*2**(s+1)))+(math.lcm(2**(s+2),3*2**(s+1))+math.gcd(2**(s+2),3*2**(s+1)))} for s in range(7)]
# A zero diagonal and nonzero cross-entry rule out positive semidefiniteness of the transformed matrix.
checks['psd_obstruction']={'indices':[1,2],'matrix':[[2,1],[1,0]],'determinant':-1}
# Exact root-log-concavity, with no floating-point roots or logarithms.
m=[1,1]
for n in range(1,201):m.append(((2*n+3)*m[n]+3*n*m[n-1])//(n+3))
t=[];v=0
for n,x in enumerate(m):v=x-v;t.append(v)
root=[]
for n in range(10,201):
 root.append(t[n]**(2*(n*n-1))>=t[n-1]**(n*(n+1))*t[n+1]**(n*(n-1)))
checks['motzkin_root_centers']=[10,200];checks['motzkin_root_pass']=all(root)
(p/'checks.json').write_text(json.dumps(checks,indent=2));print('PASS: 2304 transform entries,',len(samples),'modular ranks, 191 exact root tests; no universal proof')

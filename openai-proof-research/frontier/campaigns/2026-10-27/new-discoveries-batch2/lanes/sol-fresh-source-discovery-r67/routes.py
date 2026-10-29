import math,json,pathlib
from fractions import Fraction as F
P=pathlib.Path(__file__).resolve().parent
N=100
fac=[math.factorial(n) for n in range(N+2)]
g=[0]+[sum(d*d for d in range(1,n+1) if n%d==0) for n in range(1,N+2)]
def add(a,b,scale=1):
 c=a[:]+[0]*max(0,len(b)-len(a))
 for i,v in enumerate(b):c[i]+=scale*v
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def power(a,k):
 r=[1]
 while k:
  if k%2:r=mul(r,a)
  k//=2
  if k:a=mul(a,a)
 return r
def shift(a,s):
 r=[0]
 for v in a[::-1]:r=add([0]+r,[s*t for t in r]);r[0]+=v
 return r
A=[[1]]
for n in range(1,N+2):
 v=[0]*(n+1)
 for k in range(1,n+1):
  c=g[k]*fac[n-1]//fac[n-k]
  for j,t in enumerate(A[n-k]):v[j+1]+=c*t
 A.append(v)
out={'N':N,'derivative':[],'base_delta':[],'turan':[]}
for n in range(1,N+1):
 da=[(j+1)*v for j,v in enumerate(A[n][1:])];db=[(j+1)*v for j,v in enumerate(A[n+1][1:])]
 d=add([v*(n+1) for v in mul(da,A[n+1])],mul(A[n],db),-n)
 s=shift(d,1)
 neg=[i for i,v in enumerate(s) if v<0]
 rawneg=[i for i,v in enumerate(d) if v<0]
 out['derivative'].append({'n':n,'negative_raw':rawneg,'negative_shift1':neg,'constant_shift1':str(s[0]),'degree':len(d)-1})
 if n<=12:
  # Delta * (n!)^(n+1)*(n+1)^n
  q=add([v*(n+1)**n for v in power(A[n],n+1)],power(A[n+1],n),-fac[n])
  s=shift(q,5 if n<6 else 1)
  out['base_delta'].append({'n':n,'shift':5 if n<6 else 1,'neg':[i for i,v in enumerate(s) if v<0],'constant':str(s[0]),'degree':len(q)-1})
 if n>=2:
  t=add([v*(n+1) for v in mul(A[n],A[n])],mul(A[n-1],A[n+1]),-n)
  s=shift(t,1)
  out['turan'].append({'n':n,'negative_shift1':[i for i,v in enumerate(s) if v<0]})
(P/'routes.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'derivative_fails':[(r['n'],r['negative_shift1'][:5]) for r in out['derivative'] if r['negative_shift1']], 'raw_fails':[r['n'] for r in out['derivative'] if r['negative_raw']], 'base':out['base_delta'],'turan_shift_fails':[r['n'] for r in out['turan'] if r['negative_shift1']]}))

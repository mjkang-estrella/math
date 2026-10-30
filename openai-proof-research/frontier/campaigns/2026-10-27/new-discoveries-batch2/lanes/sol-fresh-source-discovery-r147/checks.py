import json,math,time
from fractions import Fraction as F
from pathlib import Path
import sympy as s
L=Path(__file__).resolve().parent
start=time.monotonic();out={'scope':'bounded LLL heuristic, not exhaustive; exact checks certify only listed polynomials','degrees':[],'failures':[]}
# floor(phi^n): Lucas_n minus (-1)^n phi^-n, for n>=1.
luc=[2,1]
for n in range(1,1600):luc.append(luc[-1]+luc[-2])
def bound(n):return 1 if n==0 else luc[n]-(n%2==0)
def certify(c):
 d=len(c)-1
 while d and not c[d]:d-=1
 c=c[:d+1];N=max(64,64*d)
 C=sum((F(abs(x),math.factorial(k)) for k,x in enumerate(c)),F(0))
 tail=C*N**d<=F(3,2)**N and F(N+1,N)**d<=F(3,2)
 worst=None;ok=True;vals=[]
 for n in range(N+1):
  v=sum(x*math.comb(n,k) for k,x in enumerate(c) if k<=n)
  if abs(v)>bound(n):ok=False
  if n<=4*d:vals.append(v)
 return dict(c=c,degree=d,finite_N=N,finite_pass=ok,tail_pass=tail,global_pass=ok and tail,initial_values=vals)
for d in [2,4,6,8,10,12,16,20]:
 if time.monotonic()-start>170:out['failures'].append('170s self cutoff before next degree');break
 N=6*d+10;Q=2**(N+24)
 # Integer weight using Lucas numbers; weights approximate phi^-n within
 # a fixed factor at small n. They select candidates only.
 weights=[Q//max(1,bound(n)) for n in range(N+1)]
 M=s.Matrix([[math.comb(n,k)*weights[n] if n>=k else 0 for n in range(N+1)] for k in range(d+1)])
 try:
  reduced,T=M.lll_transform(delta=F(3,4))
  results=[certify([int(T[j,k]) for k in range(d+1)]) for j in range(d+1)]
  out['degrees'].append(dict(d=d,lattice_columns=N+1,candidates=results))
  print(d,[(r['degree'],r['global_pass']) for r in results],flush=True)
 except Exception as e:out['failures'].append(dict(d=d,error=repr(e)));print('failure',d,repr(e),flush=True)
out['seconds']=time.monotonic()-start
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')

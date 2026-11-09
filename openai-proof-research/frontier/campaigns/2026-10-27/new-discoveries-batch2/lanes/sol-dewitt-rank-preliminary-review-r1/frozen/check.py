import json
from math import isqrt
from collections import Counter
from pathlib import Path
P=Path(__file__).resolve().parent
M=3200
divs=[[] for _ in range(M+1)]
for d in range(1,M+1):
 for n in range(d,M+1,d):divs[n].append(d)
def parts(N):
 for a in range(2,N):
  for c in range(1,(N-1)//a+1):
   r=N-a*c
   for b in divs[r]:
    if b>=a:break
    yield a,c,b,r//b
def conj(p):
 a,c,b,d=p
 return c+d,b,c,a-b
def swap(p):
 a,c,b,d=p
 return (c,a,d,b) if c>d else (d,b,c,a)
def typ(p):return ''.join('O' if z%2 else 'E' for z in p)
def S(p):
 a,c,b,d=p
 return a%4==2 and c%2==1 and b%2==1 and d%4==0 and a!=2*b
checks=Counter();source=[]
Ns=sorted(set(range(2,601,4))|{A*n+B for A,B in [(16,14),(36,30),(72,42),(196,70),(252,114)] for n in range(12)})
for N in Ns:
 ps=set(parts(N));counts=[[0]*4 for _ in range(2)];cl=Counter()
 for p in ps:
  a,c,b,d=p;cl[typ(p)]+=1
  counts[0][(a-c-d)%4]+=1;counts[1][(a+b-2*c-d)%4]+=1
  q=conj(p);assert q in ps and conj(q)==p
  assert (q[0]-q[1]-q[3]+a-c-d)%4==0
  assert (q[0]+q[2]-2*q[1]-q[3]+a+b-2*c-d)%4==0
  checks['conjugate_partition_checks']+=1
  if S(p):
   q=conj(swap(conj(p)));assert S(q) and q in ps and conj(swap(conj(q)))==p
   checks['S_involution_checks']+=1
 E2=counts[1][0]+counts[1][2];E1=counts[0][0]+counts[0][2]
 X=cl['OEOE'];Y=cl['OEEO'];Z=cl['EOEO']
 assert E2==2*X+Y and E1==2*Z+Y
 assert 2*(Z-X)==sum(divs[N//2])-len(divs[N//2])
 assert (E2-2*sum(S(p) for p in ps))%4==0
 checks['exact_class_and_divisor_identities']+=1
 nonsq=all(k*k+(isqrt(N-k*k))**2!=N for k in range(isqrt(N)+1))
 if nonsq:
  m=N//2;pred=len(divs[m]) if m%4==1 else 0
  assert (E2-pred)%4==0
  checks['nonsum_two_squares_formula']+=1
 if N<=100:
  brute={(a,c,b,d) for a in range(2,N) for b in range(1,a) for c in range(1,N//a+1) for d in range(1,N//b+1) if a*c+b*d==N}
  assert brute==ps;checks['independent_brute_counts']+=1
 for A,B in [(16,14),(36,30),(72,42),(196,70),(252,114)]:
  if N>=B and (N-B)%A==0:
   assert E2%4==0 and (len(ps)-E2)%4==0
   if A!=16:assert E1%4==0 and (len(ps)-E1)%4==0
   source.append({'N':N,'A':A,'rank':counts[0],'rank2':counts[1]});checks['source_progression_checks']+=1
print(json.dumps({'status':'PASS','counts':dict(checks),'N_max':max(Ns),'source_rows':source},indent=2))

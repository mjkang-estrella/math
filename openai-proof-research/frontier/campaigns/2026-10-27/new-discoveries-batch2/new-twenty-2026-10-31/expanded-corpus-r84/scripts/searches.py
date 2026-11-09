from pathlib import Path
import json,math,itertools,time
D=Path(__file__).resolve().parents[1]
mode=__import__('sys').argv[1];t=time.time();o={'mode':mode,'diagnostic_only':True}
if mode=='supervenience':
 counts={}
 for w in range(1,5):
  count=0
  for A,B,C in itertools.product(range(1<<w),repeat=3):
   forbidden=0;translated=0
   for u in range(w):
    for v in range(w):
     if (A>>u&1)==(A>>v&1) and (B>>u&1)==(B>>v&1) and (C>>u&1)!=(C>>v&1):forbidden|=1<<(u*w+v)
   for a,b in itertools.product(range(2),repeat=2):
    chi=[int((A>>u&1)==a and (B>>u&1)==b) for u in range(w)]
    for u in range(w):
     for v in range(w):
      if chi[u]==chi[v] and (chi[u] and (C>>u&1)) != (chi[v] and (C>>v&1)):translated|=1<<(u*w+v)
   assert forbidden==translated;count+=1
  counts[w]=count
 o.update(valuations=counts,relations='All directed relations implicitly covered by equality of forbidden-edge masks, including loops',counterexample_to_translation=None)
elif mode=='binomial':
 out={}
 for m in range(1,9):
  survivors=[];tested=0
  for a in range(2,21):
   for b in range(1,a*m):
    tested+=1
    if all(math.comb(a*m*n,b*n)%(a*n-1)==0 for n in range(1,26)):survivors.append([a,b])
  out[m]={'pairs_tested':tested,'survivors':survivors}
 o.update(n_range=[1,25],a_range=[2,20],m=out,limitation='Finite-n survivors do not prove universal divisibility; no finite-n failure refutes existential claim.')
elif mode=='giuga':
 N=1000000;spf=list(range(N+1))
 for p in range(2,math.isqrt(N)+1):
  if spf[p]==p:
   for n in range(p*p,N+1,p):
    if spf[n]==n:spf[n]=p
 found=[]
 for n in range(2,N+1):
  m=n;s=0
  while m>1:
   p=spf[m];pp=1
   while m%p==0:
    m//=p;pp*=p;s+=n//pp
  if spf[n]!=n and s>1 and (s-1)%n==0:found.append(n)
 o.update(n_range=[2,N],values=found,source_equation='composite n; sum_{p^j | n, j>=1} n/p^j - 1 is a positive integer multiple of n',limitation='Infinitude not finitely refutable.')
elif mode=='cube':
 import sympy
 ps=[p for p in sympy.primerange(2,201) if p%9 in [4,7,8]];found={}
 # a^3+b^3=p*c^3, nonzero integer a,b and positive c
 for p in ps:
  for c in range(1,61):
   for a in range(-300,301):
    if not a:continue
    b3=p*c**3-a**3;b=round(abs(b3)**(1/3))*(1 if b3>=0 else -1)
    if b and b**3==b3:found[p]=[a,b,c];break
   if p in found:break
 o.update(primes=ps,witnesses=found,c_range=[1,60],a_range=[-300,300],limitation='Unfound primes not refutations: denominators unbounded.')
elif mode=='alternate':
 import numpy as np
 N=12000000;s=np.ones(N+1,dtype=bool);s[:2]=False
 for i in range(2,math.isqrt(N)+1):
  if s[i]:s[i*i::i]=False
 ps=np.flatnonzero(s);ps=ps[:len(ps)//2*2];A=np.cumsum(ps[1::2]-ps[::2]);hits=[];fail=[];minratio=(1e9,None)
 for m,a in enumerate(A,1):
  if s[a]:
   k=len(hits)+1;hits.append([k,m,int(a)])
   if k>=15234:
    rhs=m*math.sqrt(2*m)*math.log(m)/math.sqrt(k*math.log(k));ratio=a/rhs
    if ratio<minratio[0]:minratio=(ratio,[k,m,int(a),rhs])
    if ratio<=1:fail.append([k,m,int(a),rhs])
 o.update(sieve_limit=N,prime_count=len(ps),sequence_terms=len(A),prime_sequence_count=len(hits),tested_k=[15234,len(hits)],minimum_ratio=minratio,failures=fail,limitation='Floating log comparison is diagnostic; no asymptotic proof.')
o['wall_seconds']=time.time()-t;(D/'outputs'/f'{mode}.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o)[:8000])

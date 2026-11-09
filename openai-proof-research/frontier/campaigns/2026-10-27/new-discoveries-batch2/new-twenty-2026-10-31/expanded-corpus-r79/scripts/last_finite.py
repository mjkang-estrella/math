import pathlib,json,itertools as it,sys,collections
from functools import lru_cache
D=pathlib.Path(__file__).resolve().parents[1]
def emit(i,o):(D/'outputs'/f'search-{i}.json').write_text(json.dumps(o,indent=2)+'\n')
mode=sys.argv[1]
if mode=='penults':
 out=[]
 for n in [2,3,4]:
  N=n*n
  @lru_cache(None)
  def terminal(S):
   for vertical in [False,True]:
    todo=[i for i in range(N) if S>>i&1 and (i//n==0 if vertical else i%n==0)];seen=set(todo)
    for i in todo:
     if (i//n==n-1 if vertical else i%n==n-1):return True
     for j in [i-n if i>=n else -1,i+n if i+n<N else -1,i-1 if i%n else -1,i+1 if i%n<n-1 else -1]:
      if j>=0 and S>>j&1 and j not in seen:seen.add(j);todo.append(j)
   return False
  @lru_cache(None)
  def ult(S):return not terminal(S) and any(terminal(S|1<<i) for i in range(N) if not S>>i&1)
  sizes=collections.Counter()
  for S in range(1<<N):
   if terminal(S):continue
   if all(ult(S|1<<i) for i in range(N) if not S>>i&1):sizes[S.bit_count()]+=1
  out.append({'side':n,'boards':1<<N,'penults_by_tokens':dict(sizes)});emit(364225,{'definition':'Def1.1 penult: nonterminal and every option is an ult, ult=nonterminal with a terminal option; terminal iff occupied orthogonal road joins opposite edges','scope':'all token subsets n=2,3,4; cannot test existence of unspecified global linear constants a,b','cases':out})
elif mode=='golomb':
 out=[]
 for k in range(6,13):
  r=k+2;L=k*k+k-1;nodes=[0];capped=[False]
  def rec(a,diffs):
   nodes[0]+=1
   if nodes[0]>200000:capped[0]=True;return None
   if len(a)==r:return a
   for x in range(a[-1]+1,L-(r-len(a)-1)+1):
    ds={x-y for y in a}
    if ds.isdisjoint(diffs):
     ans=rec(a+[x],diffs|ds)
     if ans:return ans
     if capped[0]:return None
   return None
  w=rec([0],set());out.append({'k':k,'marks':r,'length_cap':L,'nodes':nodes[0],'witness':w,'capped':capped[0]});emit(364886,{'scope':'increasing integer rulers starting0; k=6..12; cap200000 DFS nodes each; witness suffices for strict inequality, no failure claimed when capped','cases':out})
elif mode=='eta':
 N=4096;mask=(1<<(N+1))-1
 # Euler f1 from generalized pentagonal exponents.
 f=1
 for m in range(1,100):
  for e in [m*(3*m-1)//2,m*(3*m+1)//2]:
   if e<=N:f^=1<<e
 p=1
 # inversion by coefficients, bit parity
 for n in range(1,N+1):
  b=0
  for m in range(1,100):
   for e in [m*(3*m-1)//2,m*(3*m+1)//2]:
    if e<=n:b^=(p>>(n-e))&1
  if b:p|=1<<n
 def product(a,b):
  c=0
  while a:
   lo=a&-a;c^=b<<(lo.bit_length()-1);a-=lo
  return c&mask
 out=[]
 for t in range(1,32,2):
  ft=0
  for j in range(N//t+1):
   if f>>j&1:ft|=1<<(j*t)
  ft2=0
  for j in range(N//(2*t)+1):
   if f>>j&1:ft2|=1<<(j*2*t)
  g=product(product(ft,ft2),p);candidates=[]
  for A in range(1,32,2):
   for B in range(A):
    if not any(g>>n&1 for n in range(B,N+1,A)):candidates.append([A,B])
  out.append({'t':t,'odd_modulus_prefix_candidates':candidates});emit(362850,{'definition':'Gt=ft^3/f1 in F2[[q]], ft=product_(m>=1)(1-q^(tm)); exact prefix','scope':'odd t1..31; coefficients n0..4096; odd moduli A1..31, all residues B0..A-1. Prefix candidate is not an infinite congruence. Source itself supplies t1,A11,B1 as known quadratic-residue congruence; no new credit.','cases':out})
elif mode=='beta':
 N=2048;r=4;bits=[]
 for j in range(N):
  bits.append(r%2);r=(r*(r-1)//2)%(1<<(N-j-1)) if j<N-1 else 0
 out={}
 for l in range(1,7):out[l]=dict(collections.Counter(''.join(map(str,bits[i:i+l])) for i in range(N-l+1)))
 emit(357444,{'definition':'a0=4, a(n+1)=a(n)(a(n)-1)/2; diminishing precision computes exact first2048 parity bits','scope':'first2048 bits, overlapping block histograms lengths1..6; no finite histogram refutes or proves limiting normality','prefix':''.join(map(str,bits)),'histograms':out})

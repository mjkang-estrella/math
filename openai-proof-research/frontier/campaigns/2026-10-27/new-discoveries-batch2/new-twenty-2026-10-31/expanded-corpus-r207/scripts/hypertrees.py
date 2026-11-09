from pathlib import Path
import random,itertools,json,time
L=Path(__file__).resolve().parents[1];random.seed(207);start=time.monotonic()
def rank(A,p=1009):
 A=[r[:] for r in A];i=0
 for j in range(len(A[0])):
  k=next((k for k in range(i,len(A)) if A[k][j]%p),None)
  if k is None:continue
  A[i],A[k]=A[k],A[i];z=pow(A[i][j]%p,-1,p);A[i]=[x*z%p for x in A[i]]
  for k in range(i+1,len(A)):
   z=A[k][j]%p
   if z:A[k]=[(x-z*y)%p for x,y in zip(A[k],A[i])]
  i+=1
  if i==len(A):break
 return i
def irreducible(T,n):
 masks=[sum(1<<v for v in t) for t in T];U=[0]*(1<<len(T))
 for bits in range(1,len(U)):
  b=bits&-bits;U[bits]=U[bits-b]|masks[b.bit_length()-1];s=bits.bit_count()
  if U[bits].bit_count()<s+2+(2<=s<=n-3):return False
 return True
out=[]
for n in [11,12,13]:
 samples=[];draws=0
 while len(samples)<50 and draws<30000 and time.monotonic()-start<100:
  draws+=1;degrees=[2]*n
  for _ in range(n-6):degrees[random.randrange(n)]+=1
  stubs=[v for v in range(n) for _ in range(degrees[v])];random.shuffle(stubs);T=[tuple(sorted(stubs[j:j+3])) for j in range(0,len(stubs),3)]
  if any(len(set(t))!=3 for t in T) or len(set(T))!=len(T):continue
  if not irreducible(T,n):continue
  E=sorted(set(e for t in T for e in itertools.combinations(t,2)));A=[[0]*len(E) for _ in range(2*n)]
  for k,(u,v) in enumerate(E):A[u][k]=A[v][k]=1;A[n+u][k]=pow(u-v,-1,1009);A[n+v][k]=pow(v-u,-1,1009)
  kap=rank(A[:n]);r=rank(A);samples.append({'triples':T,'edges':E,'incidence_rank_mod1009':kap,'scattering_rank_mod1009_at_x_i_equals_i':r,'target_rank':kap+n-3})
 row={'n':n,'draws':draws,'sample_count':len(samples),'samples':samples};out.append(row);print(n,draws,len(samples),{(s['scattering_rank_mod1009_at_x_i_equals_i'],s['target_rank']) for s in samples},flush=True)
(L/'outputs/hypertrees.json').write_text(json.dumps(out,indent=2))

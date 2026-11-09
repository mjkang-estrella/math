import random,time,json,pathlib,itertools
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(342834);start=time.monotonic();out=[]
def cut(A):
 n=len(A);best=n*n
 # Exact every nonempty proper directed cut.
 for S in range(1,(1<<n)-1):
  v=S;c=0
  while v:
   bit=v&-v;v-=bit;c+=(A[bit.bit_length()-1]&~S).bit_count()
  best=min(best,c)
 return best

def ham(A):
 n=len(A);dp={1:1}
 # dp[visited] = bitset of possible path endpoints, path starts at 0.
 for S in range(1,1<<n,2):
  ends=dp.get(S,0)
  while ends:
   bit=ends&-ends;ends-=bit;i=bit.bit_length()-1
   nxt=A[i]&~S
   while nxt:
    b=nxt&-nxt;nxt-=b;dp[S|b]=dp.get(S|b,0)|b
 return any(A[i]&1 for i in range(1,n) if dp.get((1<<n)-1,0)>>i&1)
trials=0
for n in range(8,14):
 for k in range(5,min(9,n-1)):
  for t in range(35):
   trials+=1;A=[0]*n
   for i in range(n):
    for j in range(i):
     r=rng.random();sym=.65 if t%2 else .85
     if r<sym:A[i]|=1<<j;A[j]|=1<<i
     elif rng.randrange(2):A[i]|=1<<j
     else:A[j]|=1<<i
   if min(min(x.bit_count() for x in A),min(sum(a>>i&1 for a in A) for i in range(n)))<k+1:continue
   lam=cut(A)
   if lam<k+1:continue
   arcs=[(i,j) for i in range(n) for j in range(n) if A[i]>>j&1]
   F=rng.sample(arcs,k);B=A.copy()
   for i,j in F:B[i]&=~(1<<j)
   h=ham(B);out.append({'n':n,'k':k,'D_rows':A,'removed':F,'exact_arc_connectivity':lam,'hamilton_cycle_exists':h})
   if not h:print('NO HAMILTON CYCLE (not a refutation)',out[-1],flush=True)
   if time.monotonic()-start>105:break
  if time.monotonic()-start>105:break
 if time.monotonic()-start>105:break
(D/'semicomplete-search.json').write_text(json.dumps({'seed':342834,'trials':trials,'instances':out},indent=2)+'\n')
print('trials',trials,'eligible',len(out),'hamilton_certified',sum(x['hamilton_cycle_exists'] for x in out),'elapsed',time.monotonic()-start,flush=True)

import itertools,json,pathlib,math
from fractions import Fraction
L=pathlib.Path(__file__).resolve().parent
def prime(n):return n>1 and all(n%d for d in range(2,math.isqrt(n)+1))
q=next(13*k+1 for k in range(77000,78000) if prime(13*k+1))
z=next(pow(a,(q-1)//13,q) for a in range(2,q) if pow(a,(q-1)//13,q)!=1)
assert pow(z,13,q)==1
S=[0,1,5,8,12]
def det(a):
 a=[r[:] for r in a];v=1;n=len(a)
 for i in range(n):
  j=next((j for j in range(i,n) if a[j][i]),None)
  if j is None:return 0
  if j!=i:a[i],a[j]=a[j],a[i];v=-v
  c=a[i][i];v=v*c%q
  for j in range(i+1,n):
   t=a[j][i]*pow(c,-1,q)%q
   for k in range(i,n):a[j][k]=(a[j][k]-t*a[i][k])%q
 return v%q
minors=[det([[pow(z,s*j,q) for s in S] for j in J]) for J in itertools.combinations(range(1,13),5)]
assert len(minors)==792 and all(minors)
adj=[{(i+s)%13 for s in S if s} for i in range(13)]
assert all(j==i or j in adj[i] or adj[i]&adj[j] for i in range(13) for j in range(13))
transfer=[[Fraction(int(i==j or j in adj[i])) for j in range(13)] for i in range(13)]
for t in range(13):
 for b in adj[t]:
  for s in adj[b]:
   if s!=t and s not in adj[t]:transfer[t][s]+=Fraction(1,len(adj[s]&adj[t]))
assert all(x==1 for r in transfer for x in r)
# Diameter-three Cayley graphs: test the naive equal-shortest-path factorization.
fail=[]
for n in range(9,32):
 for steps in itertools.combinations(range(1,(n+1)//2),2):
  A=[{(i+d)%n for d in {*steps,*(-s for s in steps)}} for i in range(n)]
  dist=[]
  for s in range(n):
   d={s:0};todo=[s]
   for v in todo:
    for w in A[v]:
     if w not in d:d[w]=d[v]+1;todo.append(w)
   dist.append(d)
  if len(dist[0])<n or max(dist[0].values())!=3:continue
  def count(s,t):return sum(t in A[b] for a in A[s] for b in A[a])
  for a in range(n):
   for b in sorted(A[a]):
    for ss in itertools.combinations(sorted(A[a]),2):
     for tt in itertools.combinations(sorted(A[b]),2):
      if all(dist[s][t]==3 for s in ss for t in tt):
       C=[[count(s,t) for t in tt] for s in ss]
       if C[0][0]*C[1][1]!=C[0][1]*C[1][0]:
        fail.append(dict(n=n,steps=steps,middle=[a,b],sources=ss,targets=tt,counts=C));break
     if fail:break
    if fail:break
   if fail:break
  if fail:break
 if fail:break
assert fail
out=dict(prime=q,root=z,support=S,nonzero_minors=len(minors),diameter=2,diameter_two_transfer_exact=True,naive_diameter_three_rank_one_failure=fail[0])
(L/'exact-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

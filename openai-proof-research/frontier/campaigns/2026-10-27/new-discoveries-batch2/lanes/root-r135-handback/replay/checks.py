import json,random,time,itertools
from pathlib import Path
L=Path(__file__).resolve().parent
def solve(adj,mp):
 n=len(adj);N=1<<n;bad=set();dist=[]
 for u in range(n):
  d=[99]*n;d[u]=0;q=[u]
  for v in q:
   for w in range(n):
    if adj[v]>>w&1 and d[w]==99:d[w]=d[v]+1;q.append(w)
  dist.append(d)
 if mp:
  def walk(path,mask):
   for triple in itertools.combinations(path,3):bad.add(sum(1<<v for v in triple))
   last=path[-1]
   for w in range(n):
    if not (mask>>w&1) and adj[last]>>w&1 and adj[w]&(mask^(1<<last))==0:walk(path+[w],mask|(1<<w))
  for u in range(n):walk([u],1<<u)
 elif mp is False:
  for a,b,c in itertools.combinations(range(n),3):
   if any(dist[x][z]<99 and dist[x][y]+dist[y][z]==dist[x][z] for x,y,z in [(a,b,c),(a,c,b),(b,a,c)]):bad.add((1<<a)|(1<<b)|(1<<c))
 legal=bytearray(N);legal[0]=1;byv=[[] for _ in range(n)]
 for t in bad:
  for v in range(n):
   if t>>v&1:byv[v].append(t^(1<<v))
 for s in range(1,N):
  bit=s&-s;v=bit.bit_length()-1;r=s^bit
  legal[s]=legal[r] and not adj[v]&r and not any(r&t==t for t in byv[v])
 dp=bytearray([n]*(N));dp[0]=0;choice=[0]*N
 for s in range(1,N):
  if legal[s]:dp[s]=1;choice[s]=s;continue
  bit=s&-s;r=s^bit;t=r
  while True:
   u=t|bit
   if legal[u] and dp[s^u]+1<dp[s]:dp[s]=dp[s^u]+1;choice[s]=u
   if not t:break
   t=(t-1)&r
 s=N-1;parts=[]
 while s:parts.append(choice[s]);s^=choice[s]
 return dp[-1],parts
def hamming():
 out=[]
 for n in range(3,9):
  for m in range(n+1,n+5):
   for k in range(3,2*n+1):
    t=(k+1)//2;S={(i%n,j) for j in range(m) for i in range(j*t,(j+1)*t)}
    if k%2:
     # remove from a row of degree >=t+1, preserving minimum row degree t
     rs=[sum(i==a for i,j in S) for a in range(n)];a=max(range(n),key=lambda i:rs[i]);S.remove(next(x for x in sorted(S) if x[0]==a))
    rr=[sum(i==a for i,j in S) for a in range(n)];cc=[sum(j==b for i,j in S) for b in range(m)]
    assert min(rr)>=t and len(S)==m*t-(k%2)
    minval=100000
    for (i,a),(j,b) in itertools.combinations(itertools.product(range(n),range(m)),2):
     formula=cc[a]+cc[b] if i==j else rr[i]+rr[j] if a==b else rr[i]+rr[j]+cc[a]+cc[b]-2*((i,b) in S)-2*((j,a) in S)
     direct=sum(abs((i!=u)+(a!=v)-((j!=u)+(b!=v))) for u,v in S)
     assert direct==formula;minval=min(minval,direct)
    assert minval>=k;out.append([n,m,k,len(S),minval])
 return out
if __name__=='__main__':
 start=time.monotonic();rng=random.Random(135);out=[]
 for n in [7,8,9,10,11]:
  for p in [.12,.3,.5,.7,.88]:
   adj=[0]*n
   for i,j in itertools.combinations(range(n),2):
    if rng.random()<p:adj[i]|=1<<j;adj[j]|=1<<i
   bar=[((1<<n)-1)^a^(1<<i) for i,a in enumerate(adj)]
   row={'n':n,'p':p,'adj':adj}
   for mp in [False,True]:
    a,A=solve(adj,mp);b,B=solve(bar,mp)
    row['mp' if mp else 'gp']={'a':a,'b':b,'parts_G':A,'parts_complement':B}
    assert a+b<=n+1
   theta,_=solve(bar,None)
   row['clique_cover']=theta
   row['stronger_clique_cover_bridge']={z:row[z]['a']+theta<=n+1 for z in ['gp','mp']}
   out.append(row)
 controls=[]
 for name,n,edges in [('star6',6,[(0,i) for i in range(1,6)]),('path5',5,[(i,i+1) for i in range(4)]),('path8',8,[(i,i+1) for i in range(7)])]:
  adj=[0]*n
  for i,j in edges:adj[i]|=1<<j;adj[j]|=1<<i
  bar=[((1<<n)-1)^a^(1<<i) for i,a in enumerate(adj)]
  row=dict(name=name,n=n,adj=adj)
  for mp in [False,True]:
   a,A=solve(adj,mp);b,B=solve(bar,mp);row['mp' if mp else 'gp']=dict(a=a,b=b,A=A,B=B)
  controls.append(row)
 result=dict(random_graphs=out,controls=controls,hamming=hamming(),scope='25 fixed-seed graph samples and 3 controls only; exact subset-coloring DP for each; Hamming constructions diagnostics only')
 (L/'check-results.json').write_text(json.dumps(result,indent=2));print('graphs',len(out),'hamming',len(result['hamming']),'seconds',time.monotonic()-start)

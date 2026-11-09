import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
out=[]
# All order ideals encoded by weakly decreasing row lengths, closed grid neighbourhood.
for m in range(2,17):
 for n in range(2,min(m,7)+1):
  if m+n>22:continue
  nu=[m*n]*(m*n+1);count=0
  for asc in itertools.combinations_with_replacement(range(n+1),m):
   rows=asc[::-1];s=sum(rows);nb=0
   for i,r in enumerate(rows):nb+=max(min(n,r+1) if r else 0,rows[i-1] if i else 0,rows[i+1] if i+1<m else 0)
   nu[s]=min(nu[s],nb);count+=1
  N=m*n;dp=[0]*(N+1);nxt=[None]*(N+1)
  for s in range(N-1,0,-1):
   choices=range(max(s+1,nu[s]),N+1)
   j=max(choices,key=lambda j:dp[j]);dp[s]=min(s,N-s)+dp[j];nxt[s]=j
  best=max(range(1,N+1),key=lambda s:dp[s]);chain=[];s=best
  while s is not None and s<N:chain.append(s);s=nxt[s]
  c=[sum(i+j<=l for i in range(m) for j in range(n)) for l in range(m+n-2)]
  anti=sum(min(s,N-s) for s in c)
  r=dict(m=m,n=n,ideals=count,nu=nu,maximum=dp[best],antidiagonal=anti,chain=chain,counterexample=dp[best]>anti)
  out.append(r);print(m,n,count,dp[best],anti,'COUNTEREXAMPLE' if r['counterexample'] else '',flush=True)
  (D/'outputs/chains.json').write_text(json.dumps(out,indent=2)+'\n')

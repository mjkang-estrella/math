import sys,json,time
# Exact integer Laurent polynomial multiplication, discarding only p degrees above requested bound.
m1,m2,n1,n2,n3,K,L=map(int,sys.argv[1:]);mod=2*K+1
P=[{} for _ in range(L+1)];P[0]={0:1}
def mul(j,e):
 if j==0:
  for p in P:
   old=list(p.items())
   for q,v in old:p[q+e]=p.get(q+e,0)-v
   for q in [q for q in p if not p[q]]:del p[q]
 else:
  for k in range(L,j-1,-1):
   for q,v in P[k-j].items():P[k][q+e]=P[k].get(q+e,0)-v
   for q in [q for q in P[k] if not P[k][q]]:del P[k][q]
for i in range(n1):
 for e in (mod*i+K,mod*i+K+1):mul(0,e)
for direction,m,n in [(1,m1,n2),(-1,m2,n3)]:
 for j in range(1,min(m,L)+1):
  for i in range(n):
   for e in (mod*i+K,mod*i+K+1):mul(j,direction*e)
print(json.dumps(dict(parameters=[m1,m2,n1,n2,n3,K,L],nonzero=sum(map(len,P)))),flush=True)
l=mod//4
for k,p in enumerate(P):
 bad=[(q,v) for q,v in p.items() if v*(1 if min(q%mod,(-q)%mod)<=l else -1)<0]
 print(json.dumps(dict(k=k,nonzero=len(p),bad_count=len(bad),bad_first=sorted(bad)[:5])),flush=True)

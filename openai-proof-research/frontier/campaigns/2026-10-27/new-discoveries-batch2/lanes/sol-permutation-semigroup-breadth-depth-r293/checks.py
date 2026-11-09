from pathlib import Path
from math import gcd
from heapq import heappush,heappop
import json,time
L=Path(__file__).resolve().parent
# Each pair is the coefficient and constant of k; exact inverse multiplicity.
F=[[(3,0),(3,1),(6,-1)],[(6,1),(6,2),(9,3)],[(6,1),(9,2),(9,3)],[(6,1),(6,3),(6,5)],[(6,1),(12,-4),(12,0)],[(3,1),(6,-1),(6,0)],[(3,2),(3,3),(3,4)],[(12,2),(12,4),(18,3)],[(3,2),(6,1),(6,3)],[(6,3),(6,5),(12,4)],[(6,4),(6,5),(9,6)],[(12,4),(18,3),(18,5)],[(6,5),(9,6),(9,7)],[(6,5),(12,4),(12,6)],[(12,8),(12,10),(18,15)],[(12,8),(18,13),(18,15)]]
def families(t):
 out=[]
 for i,f in enumerate(F,1):
  u,v=f[0];k,r=divmod(t[0]-v,u)
  if r==0 and k>=(2 if i==5 else 1) and tuple(x*k+y for x,y in f)==tuple(t):out.append([i,k])
 return out
def apery(t):
 a=t[0];d=[10**30]*a;d[0]=0;Q=[(0,0)]
 while Q:
  v,r=heappop(Q)
  if v!=d[r]:continue
  for g in t[1:]:
   s=(r+g)%a;w=v+g
   if w<d[s]:d[s]=w;heappush(Q,(w,s))
 return d
def dp(t,N,early=False):
 a,b,c=t;d=bytearray(N+1);d[0]=1;block=[];positives=[]
 for n in range(a,N+1):
  d[n]=d[n-a] or (n>=b and d[n-b]) or (n>=c and d[n-c])
  if d[n]:
   positives.append(n);block.append(n%3)
   if len(block)==3:
    if len(set(block))!=3 and early:return None
    block=[]
 return d,positives
def certify(t):
 A=apery(t);c=max(A)-t[0]+1;N=c+5
 d,p=dp(t,N)
 assert all(bool(d[n])==(n>=A[n%t[0]]) for n in range(N+1))
 assert p[:3]==list(t)
 bad=next((p[i:i+3] for i in range(0,len(p)-2,3) if len({x%3 for x in p[i:i+3]})!=3),None)
 return dict(triple=t,apery=A,conductor=c,cutoff=N,bad=bad,families=families(t))
def main():
 start=time.monotonic();stats=dict(raw=0,gcd_residue=0,prefix_pass=0,accepted=0);valid=[];outside=[];rows=[]
 for a in range(12,181):
  counts=[0,0]
  for b in range(a+1,2*a):
   if b%3==a%3:continue
   for c in range(b+1,2*a):
    stats['raw']+=1
    if c%3 in (a%3,b%3) or gcd(gcd(a,b),c)!=1:continue
    stats['gcd_residue']+=1
    if dp((a,b,c),min(12*a,10000),True) is None:continue
    stats['prefix_pass']+=1;counts[0]+=1
    cert=certify((a,b,c))
    if cert['bad'] is None:
     stats['accepted']+=1;valid.append(cert);counts[1]+=1
     if not cert['families']:outside.append(cert)
  rows.append([a,*counts])
  if a%30==0:print('completed',a,stats,flush=True)
 out=dict(range=[12,180],stats=stats,seconds=time.monotonic()-start,valid=valid,outside=outside,rows=rows)
 (L/'checks-result.json').write_text(json.dumps(out,indent=2));print(stats,'outside',len(outside))
if __name__=='__main__':main()

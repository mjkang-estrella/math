import sys,os,resource,json
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
from fractions import Fraction as F
E=[(0,3),(1,2),(1,3),(2,1),(2,3),(3,0),(3,1),(3,2)];deg=[1,2,2,3]
def solve(A,b):
 A=[list(r)+[v] for r,v in zip(A,b)];n=len(b)
 for i in range(n):
  k=next(k for k in range(i,n) if A[k][i]);A[i],A[k]=A[k],A[i];q=A[i][i];A[i]=[v/q for v in A[i]]
  for k in range(n):
   if k!=i:
    q=A[k][i];A[k]=[a-q*b for a,b in zip(A[k],A[i])]
 return [r[-1] for r in A]
rows=[]
for mu in [1,10,100]:
 A=[[F(i==j)-F(17,20)*(F(mu if E[j][0]==E[i][1] else 1,deg[E[i][1]]-1+mu) if E[j][1]==E[i][0] else 0) for j in range(8)]for i in range(8)]
 # above C entry: column j=(a,b), row i=(c,d): b=c weight d=a denominator deg(b)
 A=[[F(i==j)- (F(17,20)*F(mu if E[i][1]==E[j][0] else 1,deg[E[j][1]]-1+mu) if E[j][1]==E[i][0] else 0) for j in range(8)]for i in range(8)]
 b=[F(3,20)*F(1,4*deg[a])for a,c in E];y=solve(A,b);p=[sum(y[i]for i,(a,c)in enumerate(E)if a==v)for v in range(4)]
 dual=solve(list(map(list,zip(*A))),[F(a==3)for a,c in E])
 rows.append({'mu':mu,'stationary':list(map(str,y)),'projection':list(map(str,p)),'dual':list(map(str,dual))})
print(json.dumps({'edges':E,'epsilon':'17/20','rows':rows},indent=2));json.dump(rows,open('outputs/pagerank-exact.json','w'),indent=2)

"""Constructive AP obstruction; proof and ratio-certificate dependency in discovery.md."""
from pathlib import Path
from math import gcd
import json
from research import apery,rank
L=Path(__file__).resolve().parent
def failed_in(A,lo,hi):
 seq=[n for n in range(max(1,lo),hi+1) if n>=A[n%len(A)]]
 for j in range(len(seq)-2):
  T=seq[j:j+3];r=rank(A,T[0])
  if r%3==1 and len({n%3 for n in T})<3:
   assert rank(A,T[1])==r+1 and rank(A,T[2])==r+2
   return dict(triple=T,rank=r,residues=[n%3 for n in T])
def classify(a,t):
 assert a>=12 and 0<2*t<a and gcd(a,t)==1
 if t==1 and a%3==2:return dict(source='H7',k=(a-2)//3)
 if t==2 and a%6==1:return dict(source='H4',k=(a-1)//6)
 A=apery(a,t);F=max(A)-a
 if (w:=failed_in(A,1,12*a)):return dict(method='frozen-r294-prefix',**w)
 assert a>9*t and t>=3, (a,t,'ratio certificate or small-t contradiction')
 if (w:=failed_in(A,F-a-2*t-4,F+4)):return dict(method='top-gap-clusters',**w)
 assert a%2==1 and a%3==2 and t%3==1
 i=(a+2*t-1)//(2*t)+4;B=F-(i+1)*a
 w=failed_in(A,B-6*t,B)
 assert w is not None,(a,t,'universal two-row lemma contradiction')
 return dict(method='two-overlapping-gap-rows',i=i,B=B,**w)
def check(a,t):
 R=classify(a,t)
 if 'source' in R:return R
 A=apery(a,t);x,y,z=R['triple'];r=R['rank']
 assert r%3==1 and [rank(A,n) for n in [x,y,z]]==[r,r+1,r+2]
 assert all(n>=A[n%a] for n in [x,y,z])
 assert len({x%3,y%3,z%3})<3
 return R
if __name__=='__main__':
 # Regression cases exercise symbolic branches; no completeness inferred from this list.
 pairs=[(13,2),(14,1),(17,4),(41,4),(101,4),(128,7),(137,7),(299,10),(401,13),(1001,4),(1003,4),(1000,7),(1001,10),(127,2),(128,1),(12,5),(31,4),(19,2)]
 rows=[dict(a=a,t=t,result=check(a,t)) for a,t in pairs if gcd(a,t)==1 and 2*t<a]
 (L/'classification-checks.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps(rows))

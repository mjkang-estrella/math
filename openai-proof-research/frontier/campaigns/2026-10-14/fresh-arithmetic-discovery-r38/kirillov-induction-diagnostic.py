#!/usr/bin/env python3
"""MIT. Tests the explicit Kirillov bound in the asymmetric induction; not its proof."""
import importlib.util,json,sys
from pathlib import Path
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('q',p/'quotient-diagnostic.py');q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
def exceptions(m):
 n=m*(m+1)//2
 return {(n,),(1,)*n,(m,)+(1,)*(n-m),(m,2)+(1,)*(n-m-2)}
def rem4(lam,n):
 out=[]
 def rec(i,left,cur):
  if i==len(lam):
   if left==0:out.append(tuple(x for x in cur if x))
   return
  lo=lam[i+4] if i+4<len(lam) else 0
  hi=min(lam[i],cur[-1] if cur else lam[0],left)
  for v in range(hi,lo-1,-1):rec(i+1,left-v,cur+[v])
 rec(0,n,[]);return out

def kirillov(lam,m):
 from math import comb
 rho=tuple(range(m,0,-1));a=b=0
 for i in range(max(len(lam),m)):
  a+=lam[i] if i<len(lam) else 0;b+=rho[i] if i<m else 0
  if a>b:return 0
 out=1;d=0
 for i in range(sum(x>=2 for x in lam)):
  d+=(rho[i] if i<m else 0)-lam[i]
  drop=lam[i]-(lam[i+1] if i+1<len(lam) else 0)
  out*=comb(d+drop,drop)
 return out

def main(top):
 rows=[]
 for m in range(7,top+1):
  n=m*(m+1)//2;nh=(m-2)*(m-1)//2;rho=tuple(range(m,0,-1));em=exceptions(m);eh=exceptions(m-2);eh1=exceptions(m-1);bad=[];stats={}
  for lam in q.parts(n):
   if lam in em:continue
   one=q.horizontal_predecessors(lam,m)
   good1=sum(nu not in eh1 for nu in one)
   if (m-2)*good1+len(one)-good1>=m-1:
    stats['one']=stats.get('one',0)+1;continue
   k=kirillov(lam,m)
   if k>=m-1:stats['K']=stats.get('K',0)+1;continue
   nus=rem4(lam,nh);good2=sum(nu not in eh for nu in nus)
   if (m-3)*good2+len(nus)-good2>=m-1:
    stats['two_remainders']=stats.get('two_remainders',0)+1;continue
   bad.append({'lambda':lam,'K':k,'one_count':len(one),'one_good':good1,'four_strip_count':len(nus),'four_strip_good':good2,'top_four':sum(lam[:4])})
  rows.append({'m':m,'stats':stats,'bad':bad});print(m,stats,'bad',len(bad),bad[:10],file=sys.stderr)
 return rows
if __name__=='__main__':print(json.dumps(main(int(sys.argv[1]) if len(sys.argv)>1 else 8),indent=2))

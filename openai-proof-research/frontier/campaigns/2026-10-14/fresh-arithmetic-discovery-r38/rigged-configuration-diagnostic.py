#!/usr/bin/env python3
"""MIT. Exact admissibility/weight tests for explicit Kirillov configurations; finite evidence only."""
import importlib.util,json,sys,math
from pathlib import Path
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('q',p/'quotient-diagnostic.py');q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
def transpose(a):return tuple(sum(x>=i for x in a) for i in range(1,a[0]+1)) if a else ()
def weight(lam,m,nu1=None):
 a=transpose(lam); nu=[tuple(range(m,0,-1))]+[a[k:] for k in range(1,len(a)+1)]+[()]
 if nu1 is not None:nu[1]=nu1
 out=1
 for k in range(1,len(nu)-1):
  if sum(nu[k])!=sum(a[k:]):return 0
  for n in range(1,max(m,a[0])+1):
   P=sum(min(n,v) for v in nu[k-1])-2*sum(min(n,v) for v in nu[k])+sum(min(n,v) for v in nu[k+1])
   if P<0:return 0
   Q=nu[k].count(n)
   out*=math.comb(P+Q,Q)
 return out

def configs(lam,m):
 a=transpose(lam);seen={a[1:]};ans=[('max',weight(lam,m))]
 if len(a)<2:return ans
 base=[max(x-1,0) for x in lam];t=a[1]
 for first in range(1,min(4,t)):
  for amount in (1,2):
   b=base.copy();b[first-1]+=amount;b[t-1]-=amount
   if min(b)<0 or any(b[i]<b[i+1] for i in range(len(b)-1)):continue
   nu=transpose(tuple(x for x in b if x))
   if nu in seen:continue
   seen.add(nu);v=weight(lam,m,nu)
   if v:ans.append((f'move{amount}:{first}->{t}',v))
 # Width-two extra configuration: redistribute two cells from long row.
 if len(a)==2 and a[1]>=4:
  nu=(a[1]-2,2)
  if nu not in seen:
   v=weight(lam,m,nu)
   if v:ans.append(('width2-two',v))
 return ans

def main(top):
 rows=[]
 for m in range(7,top+1):
  N=m*(m+1)//2;bad=[];tested=0
  for lam in q.parts(N):
   if lam[0]>=m or sum(lam[:4])>2*m:continue
   tested+=1;cs=configs(lam,m);w=sum(v for _,v in cs)
   if w<m:bad.append({'lambda':lam,'lower':w,'configs':cs})
  rows.append({'m':m,'tested':tested,'below_m':bad});print(m,tested,len(bad),bad[:10],file=sys.stderr)
 return rows
if __name__=='__main__':print(json.dumps(main(int(sys.argv[1]) if len(sys.argv)>1 else 8),indent=2))

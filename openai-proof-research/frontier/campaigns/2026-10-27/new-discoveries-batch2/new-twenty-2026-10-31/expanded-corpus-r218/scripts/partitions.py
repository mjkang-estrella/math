from pathlib import Path
import json,sys
D=Path(__file__).resolve().parents[1]
def partitions(n,m=None):
 if n==0:yield ();return
 if m is None:m=n
 for v in range(min(m,n),0,-1):
  for t in partitions(n-v,v):yield (v,)+t
def ordcols(p):
 if not p:return ()
 right={};rightset=set()
 for c in range(p[0]-1,-1,-1):
  col={}
  for r in range(len(p)-1,-1,-1):
   if p[r]<=c:continue
   x=max(col.get(r+1,0),right.get(r,0))+1
   while x in rightset:x+=1
   col[r]=x
  right=col;rightset=set(col.values())
 w=max(rightset);res=[0]*w;res[-1]=1
 for t in range(w-1,0,-1):res[t-1]=res[t]+((t in rightset)!=((t+1) in rightset))
 return tuple(res)
assert ordcols((4,2,2,1))==(4,3,2,2,1,1,1)
rows=[]
for n in range(1,int(sys.argv[1])+1):
 count=0;bad=[]
 for p in partitions(n):
  a=ordcols(p);b=ordcols(p[:-1]);count+=1
  if len(b)>len(a) or any(u>v for u,v in zip(b,a)):bad.append({'partition':p,'ord_columns':a,'deleted_ord_columns':b})
 row={'n':n,'partitions':count,'violations':bad};rows.append(row);print(json.dumps(row),flush=True)
 (D/'logs/partitions-results.json').write_text(json.dumps(rows,indent=2))

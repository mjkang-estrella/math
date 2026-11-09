import itertools,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def states(n):
 out=[]
 def fill(pos,vertical,horiz,crosses,tiles):
  if pos==n*n:
   if all(x<0 for x in vertical):out.append(tuple(tiles))
   return
  r,c=divmod(pos,n);s=vertical[c];w=horiz
  choices=[(0,-1,-1)] if s<0 and w<0 else ([(15,s,w)] if s>=0 and w>=0 else ([(5,s,-1),(6,-1,s)] if s>=0 else [(10,-1,w),(9,w,-1)]))
  for tile,north,east in choices:
   if c==n-1 and east<0:continue
   if r==n-1 and north>=0:continue
   pair=tuple(sorted((s,w))) if tile==15 else None
   if pair in crosses:continue
   vs=vertical.copy();vs[c]=north
   fill(pos+1,vs,-1 if c==n-1 else east,crosses|{pair} if pair else crosses,tiles+[tile])
 fill(0,list(range(n)),-1,set(),[]);return out
out=[]
for n in range(1,int(sys.argv[1])+1):
 ss=states(n);parent=list(range(len(ss)))
 def root(i):
  while i!=parent[i]:parent[i]=parent[parent[i]];i=parent[i]
  return i
 def union(a,b):parent[root(a)]=root(b)
 edgecount=0
 for r in range(n-1):
  for c in range(n-1):
   window={r*n+c,r*n+c+1,(r+1)*n+c,(r+1)*n+c+1};groups={}
   for i,s in enumerate(ss):
    key=tuple(v for j,v in enumerate(s) if j not in window)
    if key in groups:union(i,groups[key]);edgecount+=1
    else:groups[key]=i
 comps=len({root(i) for i in range(len(ss))})
 print('COMPLETE',n,len(ss),edgecount,comps,flush=True);out.append([n,len(ss),edgecount,comps]);(D/'outputs/pipedream.json').write_text(json.dumps(out))

from pathlib import Path
import json,sys
from functools import lru_cache
D=Path(__file__).resolve().parents[1]
def canonical(a):
 def root(v,p):return '('+''.join(sorted(root(u,v) for u in a[v] if u!=p))+')'
 return min(root(v,-1) for v in range(len(a)))
def moments(a):
 # states: 0 root unmatched needing domination by matched parent;
 # 1 root unmatched, all children matched; 2 root matched to child.
 def visit(v,p):
  kids=[visit(u,v) for u in a[v] if u!=p]
  def mul(x,y):return (x[0]*y[0],x[1]*y[0]+x[0]*y[1])
  def plus(x,y):return(x[0]+y[0],x[1]+y[1])
  s1=(1,0);s0=(1,0)
  for c in kids:s1=mul(s1,c[2]);s0=mul(s0,plus(c[1],c[2]))
  s0=(s0[0]-s1[0],s0[1]-s1[1]);s2=(0,0)
  for j,c in enumerate(kids):
   q=(c[0][0]+c[1][0],c[0][1]+c[1][1])
   for k,d in enumerate(kids):
    if k!=j:q=mul(q,plus(d[1],d[2]))
   q=(q[0],q[1]+q[0]);s2=plus(s2,q)
  return s0,s1,s2
 z=visit(0,-1);return (z[1][0]+z[2][0],z[1][1]+z[2][1])
def diam(a):
 def far(s):
  dist={s:0};q=[s]
  for v in q:
   for u in a[v]:
    if u not in dist:dist[u]=dist[v]+1;q.append(u)
  v=max(dist,key=dist.get);return v,dist[v]
 return far(far(0)[0])[1]
def broom(n,d):
 a=[[] for _ in range(n)]
 for i in range(d-1):a[i].append(i+1);a[i+1].append(i)
 for i in range(d,n):a[0].append(i);a[i].append(0)
 return a
# correction: diameter d requires long branch d-1 plus at least one leaf, as here.
level={'()':[[]]};rows=[]
for n in range(2,int(sys.argv[1])+1):
 nxt={}
 for a in level.values():
  for v in range(n-1):
   b=[x.copy() for x in a]+[[v]];b[v].append(n-1);key=canonical(b)
   if key not in nxt:nxt[key]=b
 level=nxt;bad=[];checked=0
 for key,a in level.items():
  d=diam(a)
  if d<3 or d==4:continue
  c,s=moments(a);b=broom(n,d);bc,bs=moments(b);checked+=1
  if s*bc<bs*c or (s*bc==bs*c and key!=canonical(b)):bad.append({'adj':a,'n':n,'d':d,'count':c,'sum':s,'broom_count':bc,'broom_sum':bs})
 row={'n':n,'unlabelled_trees':len(level),'eligible':checked,'violations':bad};rows.append(row);print(json.dumps(row),flush=True)
 (D/'logs/trees-results.json').write_text(json.dumps(rows,indent=2))

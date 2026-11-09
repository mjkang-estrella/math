import json, itertools, random, sys, time
from pathlib import Path

def comp(a):
 n=len(a);return [((1<<n)-1)^a[i]^(1<<i) for i in range(n)]
def reach(a,x,S=0,y=-1):
 seen=0; todo=1<<x
 while todo:
  b=todo&-todo;todo-=b;v=b.bit_length()-1;seen|=b
  adj=a[v]
  if v==x and y>=0: adj &= ~(1<<y)
  if v==y: adj &= ~(1<<x)
  todo |= adj & ~S & ~seen
 return seen

def cuts(a):
 n=len(a);out=[]
 for x in range(n):
  for y in range(x):
   opts=[];avail=((1<<n)-1)^(1<<x)^(1<<y);s=avail
   while True:
    if not (reach(a,x,s,y)>>y&1):opts.append(s)
    if not s:break
    s=(s-1)&avail
   # Only inclusion-minimal cuts needed: rainbow is hereditary.
   opts.sort(key=int.bit_count);mins=[]
   for s in opts:
    if not any(t&s==t for t in mins):mins.append(s)
   out.append((x,y,bool(a[x]>>y&1),mins))
 return out

def valid(c,cs):
 for x,y,edge,opts in cs:
  found=False
  for s in opts:
   cols=[c[v] for v in range(len(c)) if s>>v&1];st=set(cols)
   if len(st)==len(cols) and (not edge or c[x] not in st or c[y] not in st):found=True;break
  if not found:return False
 return True

def exact(a):
 n=len(a);cs=cuts(a);count=0
 # A same-color pair with two common neighbors cannot be separated:
 # both common neighbors would have to belong to a rainbow cut between that pair of neighbors.
 conflict=[[j for j in range(i) if (a[i]&a[j]).bit_count()>=2] for i in range(n)]
 c=[0]*n
 def gen(i,m,k):
  nonlocal count
  if i==n:
   count+=1
   return c.copy() if valid(c,cs) else None
  forbidden={c[j] for j in conflict[i]}
  for col in range(min(m+1,k-1)+1):
   if col in forbidden:continue
   c[i]=col;res=gen(i+1,max(m,col),k)
   if res is not None:return res
  return None
 for k in range(1,n+1):
  res=gen(1,0,k)
  if res is not None:return k,res,count
 raise AssertionError

def g6(line):
 b=line.strip();n=b[0]-63;bits=[(v-63>>s)&1 for v in b[1:] for s in range(5,-1,-1)];a=[0]*n;t=0
 for j in range(1,n):
  for i in range(j):
   if bits[t]:a[i]|=1<<j;a[j]|=1<<i
   t+=1
 return a

def run():
 mode=sys.argv[1];out=Path(sys.argv[2]);records=[];start=time.monotonic()
 if mode=='candidate':
  a=[202,225,232,149,232,22,23,31];b=comp(a)
  for graph,c in [(a,[0,1,2,2,3,0,3,1]),(b,[0,1,0,1,2,0,2,0])]:
   assert reach(graph,0)==255 and valid(c,cuts(graph))
   records.append({'adj':graph,'supplied_coloring_valid':True,'exact':exact(graph)})
  out.write_text(json.dumps(records,indent=2));print(records,flush=True);return
 if mode=='extensions10':
  graphs=[]
  for mask in range(512):
   a=[202,481,232,149,232,278,23,31,34]+[mask]
   for i in range(9):
    if mask>>i&1:a[i]|=512
   graphs.append(a)
 elif mode=='extensions9':
  graphs=[]
  for mask in range(256):
   a=[202,225,232,149,232,22,23,31]+[mask]
   for i in range(8):
    if mask>>i&1:a[i]|=256
   graphs.append(a)
 elif mode=='atlas':
  graphs=[g6(l) for l in Path('downloads/graph-atlas/graph8.g6').read_bytes().splitlines()]
 else:
  n=int(mode);rng=random.Random(346167+n);graphs=[]
  for _ in range(1000):
   a=[0]*n
   for j in range(n):
    for i in range(j):
     if rng.getrandbits(1):a[i]|=1<<j;a[j]|=1<<i
   graphs.append(a)
 hist={};eligible=0;fail=[]
 for index,a in enumerate(graphs):
  b=comp(a);n=len(a)
  if reach(a,0)!=(1<<n)-1 or reach(b,0)!=(1<<n)-1:continue
  eligible+=1;r=exact(a);s=exact(b);key=f'{r[0]}+{s[0]}';hist[key]=hist.get(key,0)+1
  if r[0]+s[0]<n:fail.append({'index':index,'adj':a,'rvd':r,'complement_rvd':s})
  result={'mode':mode,'input_graphs':len(graphs),'processed_through_index':index,'eligible':eligible,'histogram':hist,'failures':fail,'seconds':time.monotonic()-start}
  if eligible%25==0 or index==len(graphs)-1:
   out.write_text(json.dumps(result,indent=2));print(index,eligible,len(fail),flush=True)
 out.write_text(json.dumps(result,indent=2))
if __name__=='__main__':run()

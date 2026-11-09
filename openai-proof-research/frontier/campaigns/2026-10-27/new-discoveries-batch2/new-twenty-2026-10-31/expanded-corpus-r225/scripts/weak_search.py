import itertools,random,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(225)
def weak(a):
 for v,nb in enumerate(a):
  ns=[i for i in range(len(a)) if nb>>i&1]
  if not any(not(a[x]>>y&1) and (a[x]&a[y]).bit_count()==1 for x,y in itertools.combinations(ns,2)):return False
 return True
def toggle(a,x,y):a[x]^=1<<y;a[y]^=1<<x
def subweak(a,edges,start=0,counter=None):
 counter[0]+=1
 if counter[0]>15000:return None
 if weak(a):return True
 unknown=False
 for i in range(start,len(edges)):
  x,y=edges[i]
  if a[x].bit_count()<=2 or a[y].bit_count()<=2:continue
  toggle(a,x,y);ok=subweak(a,edges,i+1,counter);toggle(a,x,y)
  if ok:return True
  if ok is None:unknown=True;break
 return None if unknown else False
def reduce(a):
 n=len(a);keys=[(sum(a[j].bit_count()==2 for j in range(n) if a[v]>>j&1),a[v].bit_count()) for v in range(n)];best=min(keys);unknown=False;ops=0
 for v in range(n):
  if keys[v]!=best:continue
  ns=[j for j in range(n) if a[v]>>j&1];need={j for j in ns if a[j].bit_count()==2};fills=[(x,y) for x,y in itertools.combinations(ns,2) if not(a[x]>>y&1) and (x in need or y in need)]
  if len(fills)>18:unknown=True;continue
  found=False
  for k in range(len(fills)+1):
   for f in itertools.combinations(fills,k):
    cover={u for e in f for u in e}
    if not need<=cover:continue
    found=True;b=a[:]
    for x,y in f:toggle(b,x,y)
    b=[sum(1<<j2 for j2,j in enumerate(u for u in range(n) if u!=v) if b[i]>>j&1) for i in range(n) if i!=v]
    edges=[(x,y) for x,y in itertools.combinations(range(n-1),2) if b[x]>>y&1];ops+=1
    ok=subweak(b,edges,counter=[0])
    if ok:return True,ops
    if ok is None:unknown=True
   if found:break
 return (None if unknown else False),ops
if __name__=='__main__':
 for n in range(6,19):
  count=passed=unknown=0
  for z in range(150):
   a=[0]*n
   for i in range(n):toggle(a,i,(i+1)%n)
   pp=[(i,j) for i,j in itertools.combinations(range(n),2) if not(a[i]>>j&1)];rng.shuffle(pp)
   for x,y in pp[:rng.randrange(len(pp)+1)]:
    toggle(a,x,y)
    if not weak(a):toggle(a,x,y)
   ok,ops=reduce(a);count+=1
   if ok:passed+=1
   elif ok is None:unknown+=1
   else:print(json.dumps({'FAIL':True,'n':n,'trial':z,'adjacency':a,'operations':ops}),flush=True);sys.exit()
  print(json.dumps({'n':n,'trials':count,'passed':passed,'unknown':unknown}),flush=True)

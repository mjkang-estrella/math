import itertools,random,json,time
random.seed(102)
def cross(a,b,c,d):
 def ori(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
 return ori(a,b,c)*ori(a,b,d)<0 and ori(c,d,a)*ori(c,d,b)<0
def test(p):
 n=len(p)
 def find(s,t):
  path=[s];left=set(range(n))-{s,t}
  def dfs():
   if not left:return not any(cross(p[path[-1]],p[t],p[a],p[b]) for a,b in zip(path,path[1:]))
   for v in sorted(left):
    if any(cross(p[path[-1]],p[v],p[a],p[b]) for a,b in zip(path,path[1:])):continue
    path.append(v);left.remove(v)
    if dfs():return True
    left.add(v);path.pop()
   return False
  return dfs()
 return [(s,t) for s,t in itertools.combinations(range(n),2) if not find(s,t)]
for n in range(3,11):
 start=time.monotonic();bad=[]
 for it in range(25):
  while True:
   p=random.sample(list(itertools.product(range(30),repeat=2)),n)
   if all((b[0]-a[0])*(c[1]-a[1])!=(b[1]-a[1])*(c[0]-a[0]) for a,b,c in itertools.combinations(p,3)):break
  f=test(p)
  if f:bad.append({'points':p,'endpoint_pairs':f})
 print(json.dumps({'n':n,'straight_line_drawings':25,'endpoint_pairs_per_drawing':n*(n-1)//2,'failures':bad,'seconds':time.monotonic()-start}),flush=True)

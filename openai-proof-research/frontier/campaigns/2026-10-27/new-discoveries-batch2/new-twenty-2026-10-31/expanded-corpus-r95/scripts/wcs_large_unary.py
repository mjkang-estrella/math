import math,json,resource,sys,time,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
ns={};L=pathlib.Path(__file__).resolve().parents[1];exec((L/'scripts/wcs.py').read_text().split('for k in range(501,1001):')[0],ns);seeds=ns['seeds'];prime=ns['prime'];sys.setrecursionlimit(3000)
for k in range(int(sys.argv[1]),int(sys.argv[2])):
 started=time.monotonic();allmask=(1<<k)-1;classes=[]
 for d in range(k):
  groups={}
  for v in range(1,k+1):g=math.gcd(d,v);groups[g]=groups.get(g,0)|1<<(v-1)
  classes.append(groups)
 pairs=[]
 for p in range(2,k+1):
  if not prime(p):continue
  a=p
  while a*p<=k:a*=p
  if k<a+a//p:pairs.append((a,a//p))
 generated=set();q=[]
 for name,s in seeds(k):t=tuple(s);generated.add(t);q.append(t)
 while q:
  s=q.pop();changes=[s[::-1]]
  for a,b in pairs:changes.append(tuple(b if v==a else a if v==b else v for v in s))
  # Source Rule 1 is only authorized on the Sophie family at its original positions.
  for a in range((k+1)//2+1,k-1):
   if prime(a) and prime(a+2) and s[a-3]==a and s[a-1]==a+2:
    b=list(s);b[a-3],b[a-1]=b[a-1],b[a-3];changes.append(tuple(b))
  for t in changes:
   if t not in generated:generated.add(t);q.append(t)
 count=0;nodes=0;miss=[]
 def dfs(dom,assigned):
  global count,nodes
  nodes+=1
  if nodes>30000 or time.monotonic()-started>22:raise RuntimeError('node or 22 second per size cap')
  if len(assigned)==k:
   count+=1;s=tuple(assigned[i] for i in range(k))
   if s not in generated:miss.append(s)
   return
  i=min((j for j in range(k) if j not in assigned),key=lambda j:dom[j].bit_count());avail=dom[i]
  while avail:
   bit=avail&-avail;avail-=bit;v=bit.bit_length();new=dom[:];ok=True
   for j in range(k):
    if j==i or j in assigned:continue
    d=abs(j-i);new[j]&=classes[d][math.gcd(d,v)]&~bit
    if not new[j]:ok=False;break
   if ok:assigned[i]=v;dfs(new,assigned);del assigned[i]
 domains=[sum(1<<(v-1) for v in range(1,k+1) if all(i%d>=k%d for d in range(2,v+1) if v%d==0)) for i in range(k)]
 try:dfs(domains,{});complete=True
 except RuntimeError:complete=False
 print(json.dumps({'k':k,'nodes':nodes,'seconds':time.monotonic()-started,'count_found':count,'generated_family_size':len(generated),'complete':complete,'not_generated':miss}),flush=True)

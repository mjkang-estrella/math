import random,json
rng=random.Random(110)
for n in [10,12,16,20]:
 cases=bad=0
 for g in range(30):
  # Rooted forest, roots minimal: a source-proved d-complete subfamily.
  lower=[0]*n
  for v in range(1,n):
   p=rng.randrange(-1,v)
   if p>=0:lower[v]=lower[p]|1<<p
  def ext():
   p=[];seen=0
   while len(p)<n:
    choices=[v for v in range(n) if not seen>>v&1 and lower[v]&~seen==0];v=rng.choice(choices);p.append(v);seen|=1<<v
   return p
  def t(p,i):
   a,b=p[i-1:i+1]
   if not (lower[a]>>b&1 or lower[b]>>a&1):p[i-1],p[i]=b,a
  def q(p,j):
   w=[i for k in range(1,j+1) for i in range(k,0,-1)]
   for i in w[::-1]:t(p,i)
  def qjk(p,j,k):q(p,k-1);q(p,k-j);q(p,k-1)
  for z in range(100):
   i,j,k=sorted(rng.sample(range(1,n+1),3))
   if i+1>=j:continue
   p=ext();r=p[:]
   for _ in range(2):qjk(r,j,k);t(r,i)
   cases+=1
   if p!=r:bad+=1
 print(json.dumps(dict(n=n,rooted_forests=30,sampled_relation_extension_pairs=cases,violations=bad,scope='known rooted-forest d-complete subfamily only; no complete d-complete classification')),flush=True)

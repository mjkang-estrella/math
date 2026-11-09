import random,json,resource,time,pathlib
resource.setrlimit(resource.RLIMIT_AS,(1024**3,)*2);resource.setrlimit(resource.RLIMIT_CPU,(45,45));random.seed(343459)
L=pathlib.Path(__file__).resolve().parent.parent
for n in range(5,15):
 count=0
 for trial in range(3000):
  A=[0]*n
  for i in range(n):
   for j in range(i):
    if random.randrange(2):A[i]^=1<<j;A[j]^=1<<i
  # Exact all-message weights, using Gray traversal
  v=0;s=0;best=2*n;bad=None
  for t in range(1,1<<n):
   k=(t&-t).bit_length()-1;s^=1<<k;v^=A[k];w=s.bit_count()+v.bit_count()
   if w<best:best=w;bad=None
   if w==best and s&v and s!=v:bad=(s,v)
  count+=1
  if bad:
   d={'n':n,'trial':trial,'rows':A,'distance':best,'S':bad[0],'vonS':bad[1]};print(json.dumps(d),flush=True);(L/'code-witness.json').write_text(json.dumps(d,indent=2)+'\n');raise SystemExit
 print('n',n,'graphs',count,'no witness',flush=True)

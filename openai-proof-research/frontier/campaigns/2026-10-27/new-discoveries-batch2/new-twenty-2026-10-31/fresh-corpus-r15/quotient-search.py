import time,random,json,resource
from diagnostics import ascount
r=random.Random(1515);resource.setrlimit(resource.RLIMIT_CPU,(50,55));t=time.monotonic()
for n in [12,16,24,32]:
 local=time.monotonic();best=-999;bw=None;trials=0
 def score(w):
  orig=ascount(w);q=max(ascount([int(x==c) for x in w]) for c in range(3));return orig-q,orig,q
 w=[r.randrange(3) for _ in range(n)];sc=score(w)
 while time.monotonic()-local<9:
  v=w.copy();v[r.randrange(n)]=r.randrange(3);s=score(v);trials+=1
  if s[0]>=sc[0] or r.randrange(70)==0:w,sc=v,s
  if s[0]>best:best=s[0];bw=v;bs=s
  if trials%300==0:w=[r.randrange(3) for _ in range(n)];sc=score(w)
 print(json.dumps(dict(n=n,trials=trials,maximum_original_minus_best_quotient=best,word=bw,counts=bs)),flush=True)
print(json.dumps(dict(seconds=time.monotonic()-t,ru_maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

import random,json,sys
p=int(sys.argv[1]);mod=1009;rng=random.Random(355824+p);I=(1,0,0,1);Z=(0,0,0,0)
def add(a,b):return tuple((x+y)%mod for x,y in zip(a,b))
def mul(a,b):
 x,y,z,w=a;u,v,s,t=b;return ((x*u+y*s)%mod,(x*v+y*t)%mod,(z*u+w*s)%mod,(z*v+w*t)%mod)
def inv(a):
 x,y,z,w=a;d=(x*w-y*z)%mod
 if not d:raise ZeroDivisionError
 d=pow(d,-1,mod);return tuple(v*d%mod for v in [w,-y,-z,x])
def rand():
 while True:
  a=tuple(rng.randrange(mod) for _ in range(4))
  try:inv(a);return a
  except ZeroDivisionError:pass
P=[(i,j) for i in range(1,p+1) for j in range(1,p+1) if i+j>p+1]
low={v:[u for u in P if u in [(v[0]-1,v[1]),(v[0],v[1]-1)]] for v in P};up={v:[u for u in P if u in [(v[0]+1,v[1]),(v[0],v[1]+1)]] for v in P}
complete=undefined=0
for trial in range(500):
 f={v:rand() for v in P};a,b=rand(),rand();g=f.copy()
 try:
  for t in range(p):
   for v in sorted(P,key=lambda x:-sum(x)):
    l=Z
    for u in low[v]:l=add(l,g[u])
    if not low[v]:l=a
    h=Z
    for u in up[v]:h=add(h,inv(g[u]))
    if not up[v]:h=inv(b)
    g[v]=mul(mul(l,inv(g[v])),inv(h))
  target={v:mul(mul(mul(mul(a,inv(b)),f[v[::-1]]),inv(a)),b) for v in P}
  if target!=g:print(json.dumps(dict(p=p,trial=trial,f={str(k):v for k,v in f.items()},a=a,b=b,result={str(k):v for k,v in g.items()},target={str(k):v for k,v in target.items()})));raise SystemExit(2)
  complete+=1
 except ZeroDivisionError:undefined+=1
print(json.dumps(dict(p=p,modulus=mod,ring='M2(F1009)',trials=500,defined=complete,undefined=undefined,finding='no failure for all defined iterations')))

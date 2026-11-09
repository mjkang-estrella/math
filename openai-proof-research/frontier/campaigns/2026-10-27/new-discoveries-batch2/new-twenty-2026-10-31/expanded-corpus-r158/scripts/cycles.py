import itertools as I,json,sys
def count(n,es):
 m=len(es);g=m-n+1
 def dependent(s):
  pa=list(range(n))
  def root(x):
   while pa[x]!=x:x=pa[x]
   return x
  for i,(a,b) in enumerate(es):
   if s>>i&1:
    a=root(a);b=root(b)
    if a==b:return True
    pa[a]=b
  return False
 def cyclic(s):
  # A nonempty edge set is a union of circuits iff it has no bridge.
  if not s:return False
  rank=lambda t: rankof(t)
  def rankof(t):
   pa=list(range(n));ans=0
   def root(x):
    while pa[x]!=x:x=pa[x]
    return x
   for i,(a,b) in enumerate(es):
    if t>>i&1:
     a=root(a);b=root(b)
     if a!=b:pa[a]=b;ans+=1
   return ans
  r=rank(s)
  return all(rank(s^(1<<i))==r for i in range(m) if s>>i&1)
 cs=[s for s in range(1,1<<m) if cyclic(s)]
 dep={};levels=[((),[(0,0)])];nodes=0
 for depth in range(g):
  nxt=[]
  for chosen,states in levels:
   for j in range(chosen[-1]+1 if chosen else 0,len(cs)):
    c=cs[j];ns=[];ok=True
    for once,multi in states:
     o=(once^c)&~multi;mu=multi|(once&c)
     if o not in dep:dep[o]=dependent(o)
     if not dep[o]:ok=False;break
     ns.append((o,mu))
    if ok:nxt.append((chosen+(j,),states+ns))
    nodes+=1
  levels=nxt
 return dict(n=n,m=m,g=g,cycles=len(cs),systems=len(levels),nodes=nodes)
for n in range(3,7):
 es=[(0,1)]+[(a,b) for b in range(2,n) for a in (0,1)]
 print(json.dumps(dict(family='book',**count(n,es))),flush=True)
print(json.dumps(dict(family='K4',**count(4,list(I.combinations(range(4),2))))),flush=True)

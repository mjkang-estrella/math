import itertools as it,json,random,time,resource
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
t=time.monotonic()
def colors(adj):
 n=len(adj)
 def rec(cs,classes,v):
  if v==n:yield classes;return
  for j,C in enumerate(classes):
   if not adj[v]&C:
    yield from rec(cs+[j],classes[:j]+[C|1<<v]+classes[j+1:],v+1)
  yield from rec(cs+[len(classes)],classes+[1<<v],v+1)
 yield from rec([],[],0)
def irc(adj,cl):
 n=len(adj)
 for vs in it.product(*[[v for v in range(n) if C>>v&1] for C in cl]):
  S=sum(1<<v for v in vs)
  for v in vs:
   if adj[v]&S:
    if not any((adj[w]|1<<w)&S==1<<v for w in range(n)):return False
 return True
counts={}; witness=None
random.seed(54)
def graphs():
 for n in range(1,7):
  pairs=list(it.combinations(range(n),2))
  for m in range(1<<len(pairs)):
   yield n,[e for j,e in enumerate(pairs) if m>>j&1]
 for n in range(7,11):
  for z in range(500):
   p=random.choice([.2,.35,.5,.65,.8]);yield n,[e for e in it.combinations(range(n),2) if random.random()<p]
for n,edges in graphs():
 adj=[0]*n
 for u,v in edges:adj[u]|=1<<v;adj[v]|=1<<u
 col=list(colors(adj));chi=min(map(len,col))
 # any IRC coloring has no edge incident to a leaf; omit these using source private-neighbor semantics
 if any(x.bit_count()==1 for x in adj):ok=[]
 else:ok=sorted(set(len(C) for C in col if irc(adj,C)))
 counts[n]=counts.get(n,0)+1
 if ok and chi not in ok:witness={'edges':edges,'n':n,'chi':chi,'irc_colors':ok};break
print(json.dumps({'mode':'all labeled n<=6 plus seeded random n7..10 IRC source Definition2','counts':counts,'witness':witness,'seconds':time.monotonic()-t}),flush=True)
# EvenQuads: exact all subsets F2^4, affine rank filter; Q(l-1) from same finite deck only.
def quad(S):
 ss=set(S);return sum((a^b^c) in ss and (a^b^c)>c for a,b,c in it.combinations(S,3))
def rank(S):
 if not S:return 0
 b={}
 for a in S:
  a^=S[0]
  while a:
   k=a.bit_length()
   if k in b:a^=b[k]
   else:b[k]=a;break
 return len(b)
Q=[0]*17;bad=[-1]*17;examples={}
for m in range(1<<16):
 S=[a for a in range(16) if m>>a&1];l=len(S);q=quad(S);Q[l]=max(Q[l],q)
 if l and rank(S)>(l-1).bit_length():
  if q>bad[l]:bad[l]=q;examples[l]=S
print(json.dumps({'mode':'all F2^4 subsets','Q':Q,'max_outside_min_affine_container':bad,'violations_against_deck_Q':[{'l':l,'set':examples[l]} for l in examples if bad[l]>Q[l-1]],'seconds':time.monotonic()-t}),flush=True)

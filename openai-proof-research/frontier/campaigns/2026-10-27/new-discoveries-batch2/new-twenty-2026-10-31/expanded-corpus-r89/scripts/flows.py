import itertools,json
# Source 2410.04389: contract each cycle of complementary 2-factor;
# edge labels 1=alpha,2=beta,3=alpha+beta, XOR conservation;
# forbid alpha/beta labels at ends of an edge of the 2-factor.
def matchings(a):
 n=len(a)
 def rec(unused,es):
  if not unused:yield es;return
  u=(unused&-unused).bit_length()-1
  for v in a[u]:
   if unused>>v&1:yield from rec(unused^(1<<u)^(1<<v),es+[(u,v)])
 yield from rec((1<<n)-1,[])
def test(a):
 seen=0;assignments=0
 for F in matchings(a):
  seen+=1;comp=[[] for _ in a];mi={v:i for i,e in enumerate(F) for v in e}
  for u in range(len(a)):
   comp[u]=[v for v in a[u] if mi[u]!=mi[v]]
  components=[];visited=set()
  for u in range(len(a)):
   if u in visited:continue
   q=[u];visited.add(u)
   for v in q:
    for w in comp[v]:
     if w not in visited:visited.add(w);q.append(w)
   components.append(q)
  for labels in itertools.product([1,2,3],repeat=len(F)):
   assignments+=1
   ok=True
   for c in components:
    parity=0
    for u in c:parity^=labels[mi[u]]
    if parity:ok=False;break
   if not ok:continue
   if any({labels[mi[u]],labels[mi[v]]}=={1,2} for u in range(len(a)) for v in comp[u]):continue
   return dict(has_flow=True,perfect_matchings_tried=seen,assignments=assignments,matching=F,labels=labels)
 return dict(has_flow=False,perfect_matchings_tried=seen,assignments=assignments)
for n in range(5,10):
 for k in range(1,(n-1)//2+1):
  a=[set() for _ in range(2*n)]
  for i in range(n):
   for u,v in [(i,(i+1)%n),(i,n+i),(n+i,n+(i+k)%n)]:a[u].add(v);a[v].add(u)
  print(json.dumps(dict(n=n,k=k,**test(a))),flush=True)

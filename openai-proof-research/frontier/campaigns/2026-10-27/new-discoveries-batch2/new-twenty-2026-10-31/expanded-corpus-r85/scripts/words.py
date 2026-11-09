import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
res=[]
for n,L in [(2,12),(3,6)]:
 A=tuple(range(2*(n-1)));letter=lambda color,i:color*(n-1)+i
 rules=[]
 for color in range(2):
  for i in range(n-1):
   for pattern in [(color,), (color,1-color), (color,1-color,color)]:
    b=tuple(letter(c,i) for c in pattern)
    if len(pattern)<=2:rules.append((b+b,b))
    for j in [i-1,i+1]:
     if 0<=j<n-1:rules.append((b+tuple(letter(c,j) for c in pattern)+b,b))
   for c in range(2):
    for j in range(n-1):
     if (c==color and abs(i-j)>=2) or (c!=color and abs(i-j)>=1):rules.append(((letter(color,i),letter(c,j)),(letter(c,j),letter(color,i))))
 W=[w for l in range(L+1) for w in itertools.product(A,repeat=l)];ix={w:i for i,w in enumerate(W)};p=list(range(len(W)))
 def root(i):
  while p[i]!=i:p[i]=p[p[i]];i=p[i]
  return i
 count=0
 for w in W:
  for a,b in rules:
   for j in range(len(w)-len(a)+1):
    if w[j:j+len(a)]==a:
     v=w[:j]+b+w[j+len(a):]
     if len(v)<=L:
      u,z=root(ix[w]),root(ix[v]);p[u]=z;count+=1
 groups={}
 for w in W:
  g=root(ix[w]);groups.setdefault(g,w)
 reps=sorted(groups.values(),key=lambda w:(len(w),w));res.append(dict(degree=n,max_word_length=L,words=len(W),witnessed_relation_edges=count,bounded_equivalence_classes=len(groups),representatives=reps,limitation='Only relation derivations staying within the length cap. Does not prove distinctness or finiteness of presented monoid.'))
 print(n,len(W),len(groups),flush=True)
(D/'outputs/341683-search.json').write_text(json.dumps(res,indent=2)+'\n')

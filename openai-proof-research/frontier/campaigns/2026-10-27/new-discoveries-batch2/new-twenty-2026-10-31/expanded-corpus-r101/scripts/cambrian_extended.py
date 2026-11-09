import itertools,sys,json,random,pathlib,functools
n=int(sys.argv[1]);D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(101)
e=[tuple(int(i==j) for j in range(n)) for i in range(n)]
pos=e[:]+[tuple(a+b for a,b in zip(e[j],e[i])) for i in range(n) for j in range(i+1,n)]+[tuple(a-b for a,b in zip(e[j],e[i])) for i in range(n) for j in range(i+1,n)]
roots=pos+[tuple(-a for a in r) for r in pos];idx={r:i for i,r in enumerate(roots)};q=len(pos);P=(1<<q)-1;NEG=P<<q
perms=[tuple(s*x for s,x in zip(sign,p)) for p in itertools.permutations(range(1,n+1)) for sign in itertools.product([1,-1],repeat=n)]
def image(w,r):
 a=[0]*n
 for x,k in zip(r,w):a[abs(k)-1]+=x*(1 if k>0 else -1)
 return tuple(a)
chambers={w:sum(1<<idx[image(w,r)] for r in pos) for w in perms}
length={w:(chambers[w]&NEG).bit_count() for w in perms}
def left(w,s):
 if s==0:return tuple(-a if abs(a)==1 else a for a in w)
 return tuple((1 if a>0 else -1)*(s+1 if abs(a)==s else s if abs(a)==s+1 else abs(a)) for a in w)
def sortable(w,c):
 prev=set(range(n))
 while length[w]:
  cur=set()
  for s in c:
   v=left(w,s)
   if length[v]<length[w]:cur.add(s);w=v
  if not cur<=prev:return False
  assert cur;prev=cur
 return True
sums=[(i,j,idx[r]) for i,a in enumerate(roots) for j,b in enumerate(roots) if (r:=tuple(x+y for x,y in zip(a,b))) in idx]
pp=[(i,j,k) for i,j,k in sums if i<q and j<q];cross=[(i,j,k) for i,j,k in sums if i>=q and j<q]
@functools.lru_cache(maxsize=100000)
def meet(A,B):
 posi=(A|B)&P;negi=(A&B)&NEG
 change=True
 while change:
  change=False
  for i,j,k in pp:
   if posi>>i&1 and posi>>j&1 and not posi>>k&1:posi|=1<<k;change=True
 change=True
 while change:
  change=False;R=posi|negi
  for i,j,k in cross:
   if negi>>i&1 and posi>>j&1 and not R>>k&1:negi^=1<<i;change=True
 R=posi|negi
 assert not any(R>>i&1 and R>>j&1 and not R>>k&1 for i,j,k in sums)
 return R
out=[]
cs=list(itertools.permutations(range(n))) if n<=3 else [tuple(range(n)),tuple(range(0,n,2))+tuple(range(1,n,2))]
for c in cs:
 lo=[w for w in perms if sortable(w,c)];hi=[w for w in perms if sortable(tuple(-a for a in w),c[::-1])];objects=set()
 for w in lo:
  a=chambers[w]&NEG
  for v in hi:
   if a&~chambers[v]==0:objects.add(a|(chambers[v]&P))
 objects=list(objects);O=set(objects);fails=[];tests=0
 pairs=itertools.combinations_with_replacement(objects,2) if n<=3 else ((rng.choice(objects),rng.choice(objects)) for _ in range(50000))
 for A,B in pairs:
  tests+=1;M=meet(A,B);J=((1<<(2*q))-1)^meet(((1<<(2*q))-1)^A,((1<<(2*q))-1)^B) if False else None
  # Join obtained by sign inversion followed by meet, which reverses weak order.
  flip=lambda R:((R&P)<<q)|((R&NEG)>>q)
  J=flip(meet(flip(A),flip(B)))
  if M not in O or J not in O:fails.append({'A':A,'B':B,'meet':M,'join':J});break
 r={'type':f'B{n}','c':c,'sortables':len(lo),'antisortables':len(hi),'intervals':len(objects),'pairs':tests,'fails':fails};out.append(r);print(r,flush=True)
(D/f'outputs/cambrian-B{n}.json').write_text(json.dumps(out,indent=2)+'\n')

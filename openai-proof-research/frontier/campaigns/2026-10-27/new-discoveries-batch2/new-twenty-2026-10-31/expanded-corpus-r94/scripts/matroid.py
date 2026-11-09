import itertools as it,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[1];rng=random.Random(9403);out=[]
def rankvec(cols):
 r=[]
 for mask in range(1<<len(cols)):
  piv={}
  for i,v in enumerate(cols):
   if not mask>>i&1:continue
   while v:
    k=v.bit_length()
    if k in piv:v^=piv[k]
    else:piv[k]=v;break
  r.append(len(piv))
 return r
def calc(cols):
 n=len(cols);N=1<<n;r=rankvec(cols);up=[1<<a for a in range(N)];down=up[:];adj=[0]*N
 for a in range(N):
  for i in range(n):
   if a>>i&1:continue
   b=a|1<<i;s,t=(a,b)if r[b]>r[a]else(b,a);up[s]|=1<<t;down[t]|=1<<s;adj[a]|=1<<b;adj[b]|=1<<a
 for k in range(N):
  for a in range(N):
   if up[a]>>k&1:up[a]|=up[k]
   if down[a]>>k&1:down[a]|=down[k]
 eq=set()
 for types in it.product(range(4),repeat=n):
  R=sum(1<<i for i,x in enumerate(types)if x==1);F=sum(1<<i for i,x in enumerate(types)if x==2);T=sum(1<<i for i,x in enumerate(types)if x==3)
  if not F or not T:continue
  if all(r[A]==r[R]+(A&F).bit_count()for A in range(N)if A&R==R and A&~(R|F|T)==0):eq.add((R,R|F|T,R|F,R|T))
 full=(1<<N)-1;counts=[0,0,0]
 def visit(yes,no):
  if yes|no==full:
   counts[0]+=1
   if not yes:return
   if any(((yes>>a&1)+(yes>>b&1)!=(yes>>c&1)+(yes>>d&1))for a,b,c,d in eq):return
   counts[1]+=1
   seen=0;todo=yes&-yes
   while todo:
    bit=todo&-todo;todo^=bit;seen|=bit;todo|=adj[bit.bit_length()-1]&yes&~seen
   if seen==yes:counts[2]+=1
   return
  u=(full&~(yes|no)).bit_length()-1
  if not up[u]&no:visit(yes|up[u],no)
  if not down[u]&yes:visit(yes,no|down[u])
 visit(0,0)
 return dict(columns=cols,rank=r[-1],upsets=counts[0],A2_binary_solutions=counts[1],certified_connected_binary_irreducible_lower_bound=counts[2],molecule_equalities=len(eq))
seen=set()
for rep in range(25):
 cols=[rng.randrange(8)for _ in range(5)]
 r=rankvec(cols)
 if tuple(r)in seen:continue
 seen.add(tuple(r));o=calc(cols);out.append(o);print(o,flush=True);(D/'outputs/matroid.json').write_text(json.dumps(out,indent=2)+'\n')

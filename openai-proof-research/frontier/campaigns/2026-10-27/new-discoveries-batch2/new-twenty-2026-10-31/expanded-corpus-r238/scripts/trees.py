import pathlib,json,math,itertools,time,sys,collections,fractions
D=pathlib.Path(__file__).resolve().parents[1]
def rootcode(g,v,p=-1):return tuple(sorted(rootcode(g,w,v) for w in g[v] if w!=p))
def canonical(g):
 deg=[len(x) for x in g];leaves=[v for v in range(len(g)) if deg[v]<=1];left=len(g)
 while left>2:
  left-=len(leaves);nxt=[]
  for v in leaves:
   for w in g[v]:
    deg[w]-=1
    if deg[w]==1:nxt.append(w)
  leaves=nxt
 return min(rootcode(g,v) for v in leaves)
def graph(c):
 g=[]
 def rec(c,p=None):
  v=len(g);g.append([])
  if p is not None:g[v].append(p);g[p].append(v)
  for x in c:rec(x,v)
 rec(c);return g
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def match(g,v=0,p=-1):
 children=[match(g,w,v) for w in g[v] if w!=p];free=[1]
 for a,b in children:free=mul(free,b)
 total=free.copy()+[0]
 for i,(a,b) in enumerate(children):
  term=a
  for j,(_,bb) in enumerate(children):
   if i!=j:term=mul(term,bb)
  for j,x in enumerate(term):
   if j+1>=len(total):total.append(0)
   total[j+1]+=x
 while len(total)>1 and total[-1]==0:total.pop()
 return free,total
def cover(g,extra):
 es=[(u,v) for u in range(len(g)) for v in g[u] if u<v];m=len(es);ans=fractions.Fraction()
 for ix in itertools.combinations_with_replacement(range(m),extra):
  ws=[1]*m
  for i in ix:ws[i]+=1
  ds=[0]*len(g);num=1;den=1
  for (u,v),w in zip(es,ws):ds[u]+=w;ds[v]+=w;num*=w;den*=math.factorial(w)**2
  for d in ds:num*=math.factorial(d-1)
  ans+=fractions.Fraction(num,den)
 ans*=2*(m+extra);assert ans.denominator==1;return int(ans)
assert cover([[1],[0,2],[1,3],[2]],0)==6
assert cover([[1],[0,2],[1,3],[2]],1)==32
level={()};summary=[]
for n in range(2,int(sys.argv[1])+1):
 t=time.monotonic();new=set()
 for c in level:
  g=graph(c)
  for v in range(n-1):
   g[v].append(n-1);g.append([v]);new.add(canonical(g));g.pop();g[v].pop()
 level=new;groups=collections.defaultdict(list)
 for c in level:
  g=graph(c);groups[tuple(match(g)[1])].append((c,g))
 cos=[v for v in groups.values() if len(v)>1];rows={'n':n,'unlabelled_trees':len(level),'ordinary_cospectral_buckets':len(cos),'ordinary_cospectral_pairs':sum(len(v)*(len(v)-1)//2 for v in cos)}
 survivors=[]
 for vs in cos:
  sub=collections.defaultdict(list)
  for c,g in vs:sub[tuple(cover(g,x) for x in range(3))].append(c)
  survivors.extend(v for v in sub.values() if len(v)>1)
 rows.update(cover012_surviving_buckets=len(survivors),cover012_surviving_pairs=sum(len(v)*(len(v)-1)//2 for v in survivors),seconds=time.monotonic()-t);summary.append(rows);print(json.dumps(rows),flush=True)
 (D/'tree-coverage.json').write_text(json.dumps(summary,indent=2)+'\n')
 (D/f'tree-survivors-{n}.json').write_text(json.dumps({'n':n,'canonical_rooted_codes':survivors},indent=2)+'\n')

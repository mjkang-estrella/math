import pathlib,json,itertools,functools,random,sys,time,math
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(168);start=time.monotonic();out=[]
def save(): (D/('outputs/'+sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2))
def pm(v):
 if not v:yield ();return
 a=v[0]
 for j,b in enumerate(v[1:],1):
  for s in pm(v[1:j]+v[j+1:]):yield ((a,b),)+s
def parts(n,m=2):
 if n==0:yield ();return
 for j in range(m,n+1):
  for t in parts(n-j,j):yield (j,)+t

def spectrum(ms,N):
 adj=[[] for _ in range(N)];n=N//2;base=n+1
 for c,m in enumerate(ms):
  for a,b in m:adj[a].append((b,base**c));adj[b].append((a,base**c))
 @functools.lru_cache(None)
 def rec(mask,skip):
  if not mask:return int(skip==0)
  if mask.bit_count()<skip:return 0
  bit=mask&-mask;v=bit.bit_length()-1;rest=mask^bit;r=rec(rest,skip-1) if skip else 0
  for w,shift in adj[v]:
   if rest>>w&1:r|=rec(rest^(1<<w),skip)<<shift
  return r
 return rec((1<<N)-1,2)
def test(ms,N):
 sp=spectrum(ms,N);n=N//2;b=n+1
 missing=[(a,c,n-1-a-c) for a in range(n) for c in range(n-a) if not (sp>>(a+c*b+(n-1-a-c)*b*b)&1)]
 if missing:
  # all K4 unions are the known excluded exception
  adj=[set() for _ in range(N)]
  for m in ms:
   for a,b in m:adj[a].add(b);adj[b].add(a)
  seen=set();sizes=[]
  for v in range(N):
   if v in seen:continue
   q={v};comp=set()
   while q:
    u=q.pop();comp.add(u);q|=adj[u]-comp
   seen|=comp;sizes.append(len(comp))
  if set(sizes)!={4}:out.append({'COUNTEREXAMPLE':ms,'N':N,'missing':missing});save();raise SystemExit
 return len(missing)
if sys.argv[1]=='matchings':
 for n in range(2,7):
  N=2*n;m1=tuple((i,i+1) for i in range(0,N,2));s1=set(m1);count=exceptions=0
  for pa in parts(n):
   m2=[];offset=0
   for p in pa:
    m2.extend((min(offset+2*j+1,offset+2*((j+1)%p)),max(offset+2*j+1,offset+2*((j+1)%p))) for j in range(p));offset+=2*p
   forbidden=s1|set(m2)
   for m3 in pm(tuple(range(N))):
    if set(m3)&forbidden:continue
    exceptions+=bool(test((m1,m2,m3),N));count+=1
  out.append({'n':n,'third_matching_tests':count,'known_K4_exceptions':exceptions,'coverage':'all labelled M3; M1 fixed; M2 representatives for alternating cycle partitions; hence exhaustive triples up to colour-preserving vertex relabelling'});save();print(out[-1],flush=True)
 for n in (7,8,9,10,12):
  count=0
  for _ in range(500):
   ms=[]
   for c in range(3):
    for retry in range(100):
     v=list(range(2*n));rng.shuffle(v);m=tuple(tuple(sorted(v[j:j+2])) for j in range(0,2*n,2))
     if not set(m)&{e for a in ms for e in a}:ms.append(m);break
   if len(ms)==3:test(ms,2*n);count+=1
  out.append({'n':n,'random_triples':count,'seed':168});save();print(out[-1],flush=True)
elif sys.argv[1]=='hypergraph':
 def ind(edges,n):return sum(all(s&e!=e for e in edges) for s in range(1<<n))
 for n in range(4,8):
  edges=[sum(1<<v for v in e) for e in itertools.combinations(range(n),3)];counts={}
  # exhaustive edge subsets only through 6 vertices
  if n<=6:
   for S in range(1<<len(edges)):
    es=[e for i,e in enumerate(edges) if S>>i&1];deg=[sum(e>>v&1 for e in es) for v in range(n)]
    if not deg[0] or len(set(deg))!=1:continue
    d=deg[0];val=ind(es,n);H=2**(2*d)+(2**d-1)*3**d
    assert val**(3*d)<=H**n,(n,es,val)
    counts[d]=counts.get(d,0)+1
  out.append({'n':n,'r':3,'exhaustive_simple_regular_hypergraphs_by_degree':counts});save();print(out[-1],flush=True)

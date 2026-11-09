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
if sys.argv[1]=='matchdeep':
 for n in range(7,9):
  N=2*n;m1=tuple((i,i+1) for i in range(0,N,2));s1=set(m1);count=exceptions=0
  for pa in parts(n):
   m2=[];offset=0
   for p in pa:
    m2.extend((min(offset+2*j+1,offset+2*((j+1)%p)),max(offset+2*j+1,offset+2*((j+1)%p))) for j in range(p));offset+=2*p
   forbidden=s1|set(m2)
   for m3 in pm(tuple(range(N))):
    if set(m3)&forbidden:continue
    exceptions+=bool(test((m1,m2,m3),N));count+=1
    if count%1000==0 and time.monotonic()-start>105:
     out.append({'n':n,'third_matching_tests':count,'partial':True,'last_cycle_partition':pa});save();raise SystemExit
  out.append({'n':n,'third_matching_tests':count,'known_K4_exceptions':exceptions,'coverage':'all labelled M3; M1 fixed; M2 representatives for alternating cycle partitions; hence exhaustive triples up to colour-preserving vertex relabelling'});save();print(out[-1],flush=True)

import pathlib,json,itertools,sys,time
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];maxn=int(sys.argv[2]);t=time.monotonic();out=[]
def connected(n,adj):
 s=1
 while True:
  z=s
  for v in range(n):
   if s>>v&1:z|=adj[v]
  if z==s:return s==(1<<n)-1
  s=z
def chordal(n,adj):
 left=(1<<n)-1
 while left:
  for v in range(n):
   if not left>>v&1:continue
   nb=adj[v]&left
   if all((nb&~(1<<u))&~adj[u]==0 for u in range(n) if nb>>u&1):left^=1<<v;break
  else:return False
 return True
masks={n:{k:[sum(1<<v for v in vs) for vs in itertools.combinations(range(n),k)] for k in range(n+1)} for n in range(3,maxn+1)}
for n in range(3,maxn+1):
 pairs=list(itertools.combinations(range(n),2));cnt=tests=0
 for bits in range(1<<len(pairs)):
  adj=[0]*n;edges=[]
  for j,(u,v) in enumerate(pairs):
   if bits>>j&1:adj[u]|=1<<v;adj[v]|=1<<u;edges.append((u,v))
  if mode=='dom':
   if len(edges)<n or not connected(n,adj):continue
   cnt+=1;spectrum=set()
   for ori in range(1<<len(edges)):
    ins=[0]*n
    for j,(u,v) in enumerate(edges):
     if ori>>j&1:u,v=v,u
     ins[v]|=1<<u
    if not all(ins):continue
    for k in range(3,n+1):
     if any(all(s&nb for nb in ins) for s in masks[n][k]):spectrum.add(k);tests+=1;break
   if spectrum and len(spectrum)!=max(spectrum)-min(spectrum)+1:
    print('FAIL',n,edges,sorted(spectrum));(D/'outputs/dom-counterexample.json').write_text(json.dumps({'n':n,'edges':edges,'spectrum':sorted(spectrum)}));sys.exit()
  else:
   comp=[((1<<n)-1)^a^(1<<v) for v,a in enumerate(adj)]
   if not chordal(n,comp):continue
   cnt+=1
   for r in range(2,n-1):
    d=r+1;circuits=set()
    for vertices in itertools.combinations(range(n),d):
     m=sum(1<<v for v in vertices);a=[adj[v]&m for v in range(n)]
     s=1<<vertices[0]
     while True:
      z=s
      for v in vertices:
       if s>>v&1:z|=a[v]
      if z==s:break
      s=z
     if s!=m:circuits.add(m)
    # complement clutter; exact recursive search over simplicial maximal subcircuits
    memo=set()
    def elim(E):
     if not E:return True
     key=tuple(sorted(E))
     if key in memo:return False
     subs={e^(1<<v) for e in E for v in range(n) if e>>v&1}
     for a in subs:
      star={e for e in E if e&a==a};N=a
      for e in star:N|=e
      if all(sum(1<<v for v in vs) in E for vs in itertools.combinations([v for v in range(n) if N>>v&1],d)):
       if elim(E-star):return True
     memo.add(key);return False
    tests+=1
    if not elim(circuits):
     print('FAIL',n,edges,r);(D/'outputs/cochord-counterexample.json').write_text(json.dumps({'n':n,'edges':edges,'r':r}));sys.exit()
  if time.monotonic()-t>105:
   out.append({'n':n,'graphs':cnt,'tests':tests,'complete':False,'last_mask':bits});(D/f'outputs/{mode}-{maxn}.json').write_text(json.dumps(out,indent=2));sys.exit()
 out.append({'n':n,'graphs':cnt,'tests':tests,'complete':True});print(out[-1],flush=True)
(D/f'outputs/{mode}-{maxn}.json').write_text(json.dumps(out,indent=2))

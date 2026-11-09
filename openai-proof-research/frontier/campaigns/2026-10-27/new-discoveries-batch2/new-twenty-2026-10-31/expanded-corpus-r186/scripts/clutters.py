import pathlib,itertools,functools,json
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186');out=[]
for n,d in [(5,3),(5,4),(6,5)]:
 edges=[sum(1<<i for i in t) for t in itertools.combinations(range(n),d)];faces=[sum(1<<i for i in t) for t in itertools.combinations(range(n),d-1)];allmask=(1<<len(edges))-1
 def clique(m,v):return all(m>>i&1 for i,e in enumerate(edges) if e&v==e)
 def simplicials(m):
  for f in faces:
   inc=sum(1<<i for i,e in enumerate(edges) if e&f==f and m>>i&1)
   if not inc:continue
   v=f
   for i,e in enumerate(edges):
    if inc>>i&1:v|=e
   if clique(m,v):yield inc
 @functools.lru_cache(None)
 def chordal(m):return not m or any(chordal(m&~inc) for inc in simplicials(m))
 def support(m):
  v=0
  for i,e in enumerate(edges):
   if m>>i&1:v|=e
  return v
 known={sum(1<<i for i,e in enumerate(edges) if e&v==e) for v in range(1<<n)};changed=True
 while changed:
  old=set(known);queue=list(known)
  while queue:
   m=queue.pop()
   for inc in simplicials(m):
    s=inc
    while s:
     t=m&~s
     if t not in known:known.add(t);queue.append(t)
     s=(s-1)&inc
  data=[(m,support(m)) for m in known]
  for m,v in data:
   for k,w in data:
    if v&w==v or v&w==w:continue
    if clique(m,v&w) and clique(k,v&w):known.add(m|k)
  changed=known!=old
 failures=[m for m in known if not chordal(m)]
 rec={'n':n,'d':d,'all_clutters':1<<len(edges),'decomposable_closure_size':len(known),'nonchordal_in_closure':failures,'all_nonchordal':sum(not chordal(m) for m in range(1<<len(edges)))};out.append(rec);print(json.dumps(rec),flush=True)
(L/'outputs/clutters.json').write_text(json.dumps(out,indent=2))

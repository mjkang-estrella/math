import pathlib,json,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def cover(full,blocks,first=None):
 by=[[] for _ in range(full.bit_length())]
 for x in set(blocks):
  for j in range(full.bit_length()):
   if x>>j&1:by[j].append(x)
 def rec(rem):
  if rem==0:return []
  opts=None
  for j in range(rem.bit_length()):
   if not rem>>j&1:continue
   o=[b for b in by[j] if b&rem==b]
   if not o:return None
   if opts is None or len(o)<len(opts):opts=o
  for b in opts:
   ans=rec(rem^b)
   if ans is not None:return [b]+ans
  return None
 if first is not None:
  z=rec(full^first)
  return None if z is None else [first]+z
 return rec(full)
if mode=='cycles':
 for v in [4,6,8]:
  es=[e for e in itertools.combinations(range(v),2) if e[0]//2!=e[1]//2];ix={e:j for j,e in enumerate(es)}
  for ell in range(4,v+1,2):
   if len(es)%ell:continue
   blocks=[]
   for co in itertools.combinations(range(v),ell):
    if sum(x%2 for x in co)!=ell//2:continue
    for rest in itertools.permutations(co[1:]):
     cyc=(co[0],)+rest
     if cyc[1]>cyc[-1]:continue
     edges=[tuple(sorted((cyc[j],cyc[(j+1)%ell]))) for j in range(ell)]
     if all(e in ix for e in edges):blocks.append(sum(1<<ix[e] for e in edges))
   ans=cover((1<<len(es))-1,blocks)
   out.append({'v':v,'ell':ell,'edges':es,'color':'vertex parity','candidate_cycles':len(blocks),'cover':ans})
   print('cycle',v,ell,'blocks',len(blocks),'found',ans is not None,flush=True)
elif mode=='matchings':
 for n,es in json.loads((D/'outputs/atlas.json').read_text()):
  if n%2:continue
  deg=[0]*n
  for a,b in es:deg[a]+=1;deg[b]+=1
  if len(set(deg))!=1:continue
  r=deg[0]
  if any(sum(((s>>a)^(s>>b))&1 for a,b in es)<r for s in range(1,1<<n) if s.bit_count()%2):continue
  blocks=[]
  for inds in itertools.combinations(range(len(es)),n//2):
   verts=[v for j in inds for v in es[j]]
   if len(set(verts))==n:blocks.append(sum(1<<j for j in inds))
  # For these small simple r-graphs test stronger class1 decomposition.
  ans=cover((1<<len(es))-1,blocks)
  out.append({'n':n,'r':r,'edges':es,'perfect_matchings':len(blocks),'class1_cover':ans,'double_cover':None if ans is None else ans+ans})
  print('rgraph',n,r,'class1',ans is not None,flush=True)
else:
 for nv,es in json.loads((D/'outputs/atlas.json').read_text()):
  if len(es)!=nv-1 or nv>6 or nv<2:continue
  n=nv-1;col={0:0}
  for _ in range(nv):
   for a,b in es:
    if a in col:col[b]=1-col[a]
    elif b in col:col[a]=1-col[b]
  A=[x for x in range(nv) if col[x]==0];B=[x for x in range(nv) if col[x]==1]
  blocks=[]
  for pa in itertools.permutations(range(n),len(A)):
   for pb in itertools.permutations(range(n),len(B)):
    mp=dict(zip(A,pa));mp.update(zip(B,pb));mask=0
    for a,b in es:
     if col[a]:a,b=b,a
     mask|=1<<(mp[a]*n+mp[b])
    blocks.append(mask)
  ans=cover((1<<(n*n))-1,blocks,blocks[0])
  out.append({'tree_order':nv,'tree_edges':es,'host_n':n,'candidate_copies':len(set(blocks)),'cover':ans})
  print('tree',es,'host',n,'found',ans is not None,flush=True)
(D/f'outputs/{mode}-covers.json').write_text(json.dumps(out))

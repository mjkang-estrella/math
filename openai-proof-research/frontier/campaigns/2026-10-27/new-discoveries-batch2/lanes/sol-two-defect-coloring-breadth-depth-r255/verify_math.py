import pathlib,json,hashlib,itertools,collections
L=pathlib.Path(__file__).parent
w=json.loads((L/'two-defect-witness.json').read_text());es=w['edges_colors'];n=112
assert len(es)==168 and len({(a,b) for a,b,c in es})==168
inc=[[] for _ in range(n)]
for i,(a,b,c) in enumerate(es):assert 0<=a<b<n and 0<=c<5;inc[a].append(i);inc[b].append(i)
assert all(len(t)==3 for t in inc)
def reachable(skip):
 seen={0};q=[0]
 while q:
  v=q.pop()
  for i in inc[v]:
   if i==skip:continue
   a,b,c=es[i];u=a+b-v
   if u not in seen:seen.add(u);q.append(u)
 return len(seen)==n
assert reachable(-1) and all(reachable(i) for i in range(168))
pal=[{es[i][2] for i in t} for t in inc];assert all(len(s)==3 for s in pal)
bad=[(a,b) for a,b,c in es if len(pal[a]|pal[b])==4];assert bad==[(20,111),(44,70)]
old=json.loads((L/'frozen'/'construction-results.json').read_text());assert [list(e[:2]) for e in es]==old['edges']
# Check every retained multipole witness directly, independent of defect pruning.
for name in ['F','C']:
 t=json.loads((L/(name+'-table.json')).read_text())
 for r in t['rows']:
  stars=[[] for _ in range(t['vertices'])]
  for (a,b),c in zip(t['edges'],r['colors']):stars[a].append(c);stars[b].append(c)
  for j,v in enumerate(t['ports']):stars[v].append(r['colors'][len(t['edges'])+j])
  assert all(len(s)==len(set(s))==3 for s in stars)
  assert r['state']==[[r['colors'][len(t['edges'])+j],sum(1<<c for c in stars[v])] for j,v in enumerate(t['ports'])]
  assert r['cost']==sum(len(set(stars[a]+stars[b]))==4 for a,b in t['edges'])
# Exact target cut-space palette invariant, independently enumerated subsets.
X=list(itertools.combinations(range(5),2));te=[(i,j) for i in range(10) for j in range(i+1,10) if set(X[i]).isdisjoint(X[j])];assert len(te)==15
def local(x,c):return next(i for i,(a,b) in enumerate(te) if x in (a,b) and c not in set(X[a])|set(X[b]))
cuts={sum(1<<i for i,(a,b) in enumerate(te) if ((s>>a)^(s>>b))&1) for s in range(1024)}
signatures=[]
for c in range(5):
 for a in range(10):
  for b in range(a+1,10):
   if c not in X[a] and c not in X[b] and len(set(X[a])&set(X[b]))==1:
    signatures.append((c,a,b,(1<<local(a,c))^(1<<local(b,c))))
assert len(signatures)==60
allowed=[(a,b) for a in signatures for b in signatures if a[3]^b[3] in cuts]
actual=[]
for u,v in bad:
 c=next(c for a,b,c in es if (a,b)==(u,v));a=X.index(tuple(sorted(set(range(5))-pal[u])));b=X.index(tuple(sorted(set(range(5))-pal[v])));actual.append((1<<local(a,c))^(1<<local(b,c)))
assert actual[0]^actual[1] in cuts
out={'pass':True,'vertices':n,'edges':len(es),'bridgeless':True,'proper':True,'abnormal_edges':bad,'same_edges_as_frozen_r253':True,'table_rows_individually_validated':True,'palette_signatures':60,'allowed_ordered_pairs':len(allowed),'allowed_per_signature':dict(collections.Counter(sum(a[3]^b[3] in cuts for b in signatures) for a in signatures)),'actual_cut_signature':actual[0]^actual[1],'non_normal_colorability':'published theorem dependency only; no DRAT replay'}
(L/'math-verification.json').write_text(json.dumps(out,indent=2));print(out)

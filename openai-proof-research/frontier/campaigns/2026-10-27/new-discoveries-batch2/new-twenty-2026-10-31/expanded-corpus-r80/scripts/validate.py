import pathlib,json,hashlib,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids)) and len(r)==40
for i,v in x.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256'];assert json.loads(b)['statement']==v['statement']
a=json.loads((D/'outputs/semigroups.json').read_text());assert [z['total'] for z in a[:11]]==[1,1,2,4,7,12,23,39,67,118,204]
for i in range(2,20):
 for t in range(2,i):assert a[i]['counts'].get(str(t),0)<a[i+1]['counts'].get(str(t),0)
 assert a[i]['counts'][str(i)]==a[i+1]['counts'][str(i)]==1
for name in ['polynomials-2-18','polynomials-19-24']:
 for o in json.loads((D/f'outputs/{name}.json').read_text()):assert o['irreducible']
assert [z['n'] for z in json.loads((D/'outputs/polynomials-19-24.json').read_text())]==[19,20,21,22]
assert not json.loads((D/'outputs/congruence.json').read_text())['failures']
assert [z['sortable'] for z in json.loads((D/'outputs/pqs.json').read_text())]==[1,2,6,24,120,685,4148]
# Independent directed BFS and subset checker for single-edge reversal obstruction.
line=next(l for l in (D/'outputs/gp-atlas-6.in').read_text().splitlines() if l.startswith('59 '));z=list(map(int,line.split()));n=z[1];e=list(zip(z[3::2],z[4::2]))
def py_gp(mask):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(e):
  if mask>>k&1:u,v=v,u
  adj[u].append(v)
 dist=[]
 for u in range(n):
  d=[99]*n;d[u]=0;q=[u]
  for a in q:
   for b in adj[a]:
    if d[b]==99:d[b]=d[a]+1;q.append(b)
  dist.append(d)
 for size in range(n,-1,-1):
  for subset in itertools.combinations(range(n),size):
   if all(dist[a][c]==99 or dist[a][c]!=dist[a][b]+dist[b][c] for a,b,c in itertools.permutations(subset,3)):return size
assert py_gp(1)==4 and py_gp(5)==6
for row in json.loads((D/'outputs/stack-3.json').read_text()):
 if row['moves'] is None:continue
 n=row['n'];c=[1]*n
 def ancestors(v):
  a=[v]
  while v:v=(v-1)//2;a.append(v)
  return a
 for u,v in row['moves']:
  au,av=ancestors(u),ancestors(v);dist=min(au.index(t)+av.index(t) for t in set(au)&set(av))
  assert c[u]>0 and c[v]>0 and dist==c[u];c[v]+=c[u];c[u]=0
 assert c[row['target']]==n
(D/'outputs/validation.json').write_text(json.dumps({'pass':True,'scope':'artifact cardinality, raw hashes/newlines, semigroup totals/comparisons, factorization flags, congruences, PQS counts, independent BFS obstruction, independent cup-move replay; numerical diagnostics only; no Lean endpoint'},indent=2)+'\n')
print('PASS: artifacts and diagnostics; no formal endpoint')

import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
x=json.loads((D/'results.json').read_text());r=json.loads((D/'reservation.json').read_text());assert len(x)==20 and set(x)==set(map(str,r['ids']))
for i,o in x.items():
 raw=(D/'raw'/(i+'.jsonl')).read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==o['provenance']['raw_sha256'];assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 for name,rec in o['source_receipts'].items():
  if 'sha256' in rec:assert hashlib.sha256((D/'sources'/name).read_bytes()).hexdigest()==rec['sha256']
 for p in o['attempt_artifacts']:assert (D/p).exists(),p
 assert not o['accepted']
atlas=json.loads((D/'outputs/atlas.json').read_text());seq=json.loads((D/'outputs/sequential.json').read_text());assert len(atlas)==len(seq)==1252
# Reconstruct atlas adjacency from graph6, independently of the NetworkX parser.
def edges(g6):
 n=ord(g6[0])-63;bits=''.join(f'{ord(c)-63:06b}' for c in g6[1:]);E=[];t=0
 for v in range(1,n):
  for u in range(v):
   if bits[t]=='1':E.append((u,v))
   t+=1
 return n,E
for row in atlas:
 n,E=edges(row['g6']);a=row['additive_witness'];s=[sum(a[v] if u==i else a[u] for u,v in E if i in (u,v)) for i in range(n)];assert all(s[u]!=s[v] for u,v in E)
for row in seq:
 n,E=edges(row['g6']);w=row['acyclic_witness'];assert len(w)==len(E);assert {tuple(sorted((u,v))) for u,v,c in w}==set(E)
 for v in range(n):
  incoming=[c for u,z,c in w if z==v];outgoing=[c for z,u,c in w if z==v];assert len(set(incoming))==len(incoming);assert sorted(outgoing)==list(range(len(outgoing)))
 # A topological elimination check also certifies every individual layer acyclic.
 rem=set(range(n))
 while rem:
  zero=[v for v in rem if all(z!=v or u not in rem for u,z,c in w)];assert zero
  rem.difference_update(zero)
for n in range(3,10):
 row=json.loads((D/f'outputs/signed{n}.json').read_text());assert row['inequality'];assert sum(row['positive'].values())==sum(row['negative'].values())==row['permutations']
for n in range(1,8):
 row=json.loads((D/f'outputs/sylvester{n}.json').read_text());S=row['subset'];assert len(S)==len(set(S))==row['m'];norm=sum(abs(sum((-1)**((a&b).bit_count()%2) for a in S)) for b in range(2**n));assert norm==row['best']==row['bound']
receipt={'results':20,'reserved_IDs_exact':True,'raw_and_source_hashes':True,'atlas_additive_witnesses_checked':1252,'sequential_witnesses_checked':1252,'sylvester_best_witnesses_checked':7,'signed_range_consistency':True,'accepted':0,'lean_endpoint':None}
(D/'outputs/validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)

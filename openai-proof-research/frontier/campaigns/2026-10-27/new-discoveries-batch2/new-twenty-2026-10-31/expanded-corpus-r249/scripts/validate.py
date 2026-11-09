import pathlib,json,hashlib,itertools,collections
L=pathlib.Path(__file__).resolve().parents[1];results=json.loads((L/'results.json').read_text());ids=json.loads((L/'reservation.json').read_text())['ids'];raw=json.loads((L/'extracted.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
assert set(results)==set(map(str,ids)) and len(results)==20
chunks={}
for i,v in results.items():
 b=(L/v['raw_path']).read_bytes();assert b.endswith(b'\n');assert sha(b)==v['provenance']['raw_sha256'];assert sha(v['statement'].encode())==v['statement_sha256'];assert json.loads(b)['statement']==v['statement'];p=pathlib.Path(v['provenance']['chunk'])
 if p not in chunks:chunks[p]=p.read_bytes();assert sha(chunks[p])==v['provenance']['chunk_sha256']
 assert chunks[p].splitlines(keepends=True)[v['provenance']['line']-1]==b
 assert v['credit_requested']==0 and v['lean_endpoint'] is None
http=0
for p in (L/'http').glob('*/receipt.json'):
 r=json.loads(p.read_text());body=p.parent/'body'
 if 'sha256' in r:assert sha(body.read_bytes())==r['sha256']
 http+=1
witnesses=0
for g in json.loads((L/'sequencing-results.json').read_text()):
 mods=g['moduli'];els=list(itertools.product(*(range(m) for m in mods)));N=len(els)
 for c in g['certificates']:
  A=c['subset'];order=c['order'];assert set(A)==set(order) and len(set(A))==len(A);assert 0 not in A
  for a in A:
   assert all(any((x+y)%m for x,y,m in zip(els[a],els[b],mods)) for b in A if b!=a)
  s=[0]*len(mods);seen=set()
  for a in order:
   s=[(x+y)%m for x,y,m in zip(s,els[a],mods)];assert tuple(s) not in seen;seen.add(tuple(s))
  assert not any(s);witnesses+=1
assert witnesses==1600
h=json.loads((L/'hanoi-results.json').read_text());assert all(v['border_without_good_shortest_path']==0 for v in h if v['pegs']==4 and v['movable_disks']>=6)
assert json.loads((L/'host-results.json').read_text())['hosts']==167960
assert all(v['mismatches']==0 for v in json.loads((L/'chocolate-96.json').read_text()))
assert [v['k'] for v in json.loads((L/'chocolate256-completed.json').read_text())]==[5,9]
o=dict(validated=True,reserved_entries=len(results),raw_line_bindings=20,http_receipts=http,independently_validated_ordering_witnesses=witnesses,lean_endpoints=0,credit=0,limits='Numerical results remain diagnostics; this validator does not prove any reserved universal conjecture.')
(L/'validation.json').write_text(json.dumps(o,indent=2));print(o)

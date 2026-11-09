import pathlib,json,hashlib,itertools as it
D=pathlib.Path(__file__).resolve().parents[1];R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(R)==set(map(str,ids)) and len(R)==20
for i,r in R.items():
 raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(r['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256'];assert r['credit']==0
zs=json.loads((D/'outputs/zspp40.json').read_text());patterns={(a,b,c) for a in range(14) for b in range(10) for c in range(8) if 3*a+4*b+5*c==39};assert len(zs)==len(patterns)==17
for r in zs:
 assert tuple(r['counts_3_4_5']) in patterns and r['found'];flat=sum(r['blocks'],[]);assert sorted(flat)==list(range(1,40));counts={3:0,4:0,5:0}
 for block in r['blocks']:
  x=0;y=0
  for v in block:x^=v//5;y+=v%5
  assert x==0 and y%5==0;counts[len(block)]+=1
 assert [counts[k] for k in (3,4,5)]==r['counts_3_4_5']
for r in json.loads((D/'outputs/torus.json').read_text()):
 if r['certificate_labels']:
  labels=r['certificate_labels'];assert sorted(labels)==list(range(1,len(labels)+1));assert all(sum(l for e,l in zip(r['edge_order'],labels) if v in e)==r['target'] for v in range(r['n']*r['m']))
sat=json.loads((D/'outputs/torus-sat-certificate.json').read_text());assert sorted(sat['labels'])==list(range(1,31));assert all(sum(l for e,l in zip(sat['edges'],sat['labels']) if v in e)==62 for v in range(15))
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['searches'])==8
assert all(x['response']['total_count']==0 for x in reg['searches'])
assert not reg['openai/math']['preprints']['truncated'];assert not reg['the-omega-institute/trureturing']['D5']['truncated'];assert not reg['the-omega-institute/trureturing']['Problems']['truncated']
report={'20_reserved_keys':True,'raw_and_statement_hashes':True,'all_17_zspp_certificates_exact':True,'torus_found_certificates_exact':True,'registry_scoped_trees_complete':True,'credit':0,'lean_endpoint':False,'limits':'Diagnostics checked with Python integer arithmetic, not a formal proof packet.'}
(D/'outputs/validation.json').write_text(json.dumps(report,indent=2));print(report)

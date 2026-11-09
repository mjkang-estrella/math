import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; H=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((D/'reservation.json').read_text());results=json.loads((D/'results.json').read_text());B=json.loads((D/'record-bindings.json').read_text());assert len(results)==40 and set(results)==set(map(str,R['ids']))
for k,row in results.items():
 raw=(D/'raw'/(k+'.jsonl')).read_bytes();x=json.loads(raw); assert raw.endswith(b'\n');assert H(raw)==row['raw_binding']['raw_sha256']==B[k]['raw_sha256'];assert x['statement']==row['literal_statement'];assert H(x['statement'].encode())==row['raw_binding']['statement_sha256'];assert H(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==row['raw_binding']['inherited_canonical_record_sha256'];assert row['accepted_credit']==row['new_unique_coverage_credit']==0 and not row['proposal'];assert row['old_disposition']==json.loads((D/'inherited-dispositions.json').read_text())[k]['disposition']
for p,want in R['prior_report_hashes'].items():assert H(pathlib.Path(p).read_bytes())==want
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status')==200:
  candidates=[x for x in p.parent.glob(p.name.replace('.receipt.json','')+'.*') if x.suffix in ['.pdf','.body','.json'] and x!=p];assert any(H(x.read_bytes())==r['sha256'] for x in candidates),p
s=json.loads((D/'registry-screen.json').read_text());p=pathlib.Path(s['cached_tree']);assert H(p.read_bytes())==s['cached_sha256'];t=json.loads(p.read_bytes());assert t['sha']==s['complete_preprint_tree'] and not t['truncated'];assert json.loads((D/'sources/registry.json').read_bytes())['sha']==s['live_head']
for term,hits in s['hits'].items():assert hits==[x['path'] for x in t['tree'] if term in x['path'].lower()]
m=json.loads((D/'manifest.json').read_text()); excluded={'manifest.json','final-receipt.json','final-check.log'};actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in excluded};assert actual==set(m)
for name,r in m.items():p=D/name;assert p.stat().st_size==r['bytes'] and H(p.read_bytes())==r['sha256'],name
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exact_id_keyed_results=40,new_primary_depth_ids=[384974,385263,385371],secondary_registry_context_ids=[385268],new_unique_coverage_credit=0,proposals=0,accepted_credit=0,lean_compilation_performed=False,manifest_files=len(m),manifest_sha256=H((D/'manifest.json').read_bytes()),original_primary_bodies_read=0,complete_dependency_audits=0,immutable_prior_report_hashes_match=True,raw_statement_canonical_hashes_match=True,registry_tree_hash_match=True,limit='This verifies artifact integrity and declared review boundaries, not a mathematical endpoint or novelty clearance.')
(D/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

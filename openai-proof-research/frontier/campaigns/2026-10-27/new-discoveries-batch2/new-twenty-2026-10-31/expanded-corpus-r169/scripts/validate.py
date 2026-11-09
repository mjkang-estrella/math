import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(map(int,r))==set(ids)
for i,o in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==o['provenance']['raw_sha256'];assert json.loads(b)['statement']==o['statement'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['discovery_credit']==0
 p=o['source_receipts']['pdf'];assert sha((D/p).read_bytes())==o['source_receipts']['pdf_sha256']
for folder in ['logs','outputs']:
 for p in (D/folder).glob('*.receipt.json'):
  o=json.loads(p.read_text());assert o['cap_reason'] is None
manifest=json.loads((D/'outputs/manifest.json').read_text());assert all(sha((D/p).read_bytes())==s for p,s in manifest.items())
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['github_queries'])==8
receipt={'validation':'PASS','entries':len(r),'credit':0,'required_files':{p:sha((D/p).read_bytes()) for p in ['SUMMARY.md','CANDIDATE.md','results.json','outputs/registry-screen.json']},'search_outputs':{p.name:{'tested':o.get('tested'), 'unknown_count':len(o.get('unknown',[])), 'counterexamples':o.get('counterexamples')} for p in (D/'outputs').glob('*.json') if p.stem in ['pcf','pocf','total','extension','spectral','radical','radical4','inversion','immersion','contain','structured','fort'] for o in [json.loads(p.read_text())]}}
(D/'outputs/final-validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

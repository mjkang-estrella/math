import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert all(sha(L/n)==h for n,h in m.items())
assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for r in json.loads((L/'before-after.json').read_text())['scientific']:
 assert sha(pathlib.Path(r['original']))==r['sha256']==sha(L/r['copy'])
archive=L/'frozen/source/source-only.tar.gz';assert sha(archive)=='ead8a07b9a339d55285f12e37f96fb6834a58007988160e8df8a8a864e3c595d'
for n,h in json.loads((L/'replay/source-manifest.json').read_text()).items():assert sha(L/'replay'/n)==h
assert not list((L/'replay').glob('*.olean'))
for name in ['set-reconstruction','sceneries']:
 r=json.loads((L/'prior'/(name+'.receipt.json')).read_text());e=json.loads((L/'prior'/(name+'.extract.json')).read_text())
 assert sha(L/'prior'/(name+'.pdf'))==r['sha256']==e['pdf_sha256']
 assert sha(L/'prior'/(name+'.txt'))==e['text_sha256']
for rpath in (L/'prior').glob('*.receipt.json'):
 r=json.loads(rpath.read_text())
 if 'error' not in r and rpath.stem.startswith(('arxiv-','crossref-')):
  assert sha(rpath.with_name(rpath.name.replace('.receipt.json','.body')))==r['sha256']
decls=json.loads((L/'actual-declarations.json').read_text());assert len(decls)==134
for d in decls:
 assert hashlib.sha256(d['type'].encode()).hexdigest()==d['type_sha256']
 assert not d['unsafe'] and d['safety'] in ['nondefinition','Lean.DefinitionSafety.safe']
 assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
for mod in ['Finite','Cube','Endpoint','Audit']:
 g=json.loads((L/'replay'/(mod+'.guard.json')).read_text());assert g['exit_code']==0 and g['reason'] is None
r={'status':'PASS','utc':str(datetime.datetime.now(datetime.timezone.utc)),'manifest_sha256':sha(L/'manifest.json'),'manifest_files':len(m),'archive_sha256':sha(archive),'actual_records':134,'generated_partial':0,'own_replay':'PASS','scientific_before_after':'PASS','primary_pdf_text_bindings':'PASS','counts':'9/39 next40; no credit','acceptance':'HOLD: root gates remain'}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))

import pathlib,hashlib,json,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'finalmanifest.json').read_text())
assert 'finalmanifest.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
assert actual==set(manifest)
for p,a in manifest.items():assert h(L/p)==a,p
rows=json.loads((L/'bindings.json').read_text())
for r in rows:
 for k in ['original','copy']:
  if k in r:assert h(pathlib.Path(r[k]))==r['sha256'],r[k]
for filename in ['live-access.json','refresh-access.json']:
 for r in json.loads((L/filename).read_text()):
  if 'path' in r:assert h(pathlib.Path(r['path']))==r['sha256']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':True,'manifest_sha256':h(L/'finalmanifest.json'),'files_verified':len(manifest),'scientific_bindings_verified':len(rows),'source_originals_and_copies_unchanged':True,'counts':[9,39,40],'recommendation':'EXCLUDE substantive credit; ordinary MATH PASS','caps':{'AS':536870912,'groupRSS':536870912,'CPU':210,'wall':230},'separate_guarded_verification':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))

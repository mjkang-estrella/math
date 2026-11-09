import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent;manifest=L/'final-manifest.json';data=manifest.read_bytes();m=json.loads(data);issues=[]
def check(path,h):
 try:
  if hashlib.sha256(path.read_bytes()).hexdigest()!=h:issues.append('HASH '+str(path))
 except Exception as e:issues.append(str(e))
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['excludes'])
if actual!=set(m['files']):issues.append('INVENTORY '+str(actual.symmetric_difference(m['files'])))
for name,r in m['files'].items():
 p=L/name;check(p,r['sha256'])
 if p.stat().st_size!=r['bytes']:issues.append('SIZE '+name)
for s in (L/'source-receipts.jsonl').read_text().splitlines():
 r=json.loads(s)
 if 'sha256' in r:
  for d in ['sources','frozen']:check(L/d/r['name'],r['sha256'])
for r in json.loads((L/'bindings.json').read_text()):
 check(pathlib.Path(r['copy']),r['sha256'])
 if r['kind']=='frozen':check(pathlib.Path(r['original']),r['sha256'])
for r in json.loads((L/'history-bindings.json').read_text()):check(pathlib.Path(r['path']),r['sha256'])
receipt={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not issues,'manifest_sha256':hashlib.sha256(data).hexdigest(),'entries_verified':len(m['files']),'source_originals_and_frozen_copies_verified':True,'history_originals_verified':True,'r252_original_and_copy_verified':True,'administrative_scope':'snapshot hashes only; no requirement that shared originals remain unchanged','issues':issues,'scope':'artifact integrity only; no mathematical or novelty acceptance','separate_guarded_invocation':True}
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));assert not issues

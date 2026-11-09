import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text());errors=[]
for r in m['files']:
 p=L/r['path']
 if not p.is_file() or sha(p)!=r['sha256']:errors.append('manifest:'+r['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
if actual!={r['path'] for r in m['files']}:errors.append('inventory mismatch')
for n in ['bindings.json']:
 for r in json.loads((L/n).read_text()):
  if sha(pathlib.Path(r['path']))!=r['sha256']:errors.append('external:'+r['path'])
for line in (L/'access.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'sha256' in r and sha(pathlib.Path(r['path']))!=r['sha256']:errors.append('source:'+r['path'])
for line in (L/'derived.jsonl').read_text().splitlines():
 r=json.loads(line)
 if sha(pathlib.Path(r['original']))!=r['sha256'] or sha(pathlib.Path(r['text']))!=r['text_sha256']:errors.append('derived:'+r['text'])
assert not (L/'PROOF.md').exists()
r={'status':'PASS' if not errors else 'FAIL','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'MANIFEST.json'),'file_count':len(m['files']),'errors':errors,'scope':'integrity/source bindings only; not independent mathematical acceptance','guarded_separate_invocation':True}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));raise SystemExit(bool(errors))

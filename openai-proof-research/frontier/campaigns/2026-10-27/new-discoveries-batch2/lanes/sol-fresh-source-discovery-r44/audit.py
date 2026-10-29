import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent
v=json.loads((P/'provenance.json').read_text())
names={'sources/'+s for s in v['inherited_caches']['scopes']}
old=P.parent/'sol-fresh-source-discovery-r43/http.jsonl'
v['inherited_caches']['original_http_records']=[json.loads(l) for l in old.read_text().splitlines() if json.loads(l).get('file') in names]
v['audit_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
v['local_artifacts']=[{'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(P.iterdir()) if p.is_file() and p.name!='provenance.json']
for row in v['http']:
 if 'sha256' in row:
  f=P/row['file'];assert hashlib.sha256(f.read_bytes()).hexdigest()==row['sha256']
for row in v['files']:
 assert hashlib.sha256((P/row['file']).read_bytes()).hexdigest()==row['sha256']
for n in ['SUMMARY.md','discovery.md','progress.md','check.py','run.sh','checks.json']:
 assert (P/n).exists()
assert not (P/'PROOF.md').exists()
(P/'provenance.json').write_text(json.dumps(v,indent=2))
print('PASS source hashes; required artifacts; no PROOF.md; copied inventory dates retained')

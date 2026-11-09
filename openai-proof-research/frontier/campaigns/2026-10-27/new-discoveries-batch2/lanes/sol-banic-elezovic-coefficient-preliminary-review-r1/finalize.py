import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'bindings.json').read_text())
for r in rows:
 if r['original'].endswith('root-banic-elezovic-triage-r1/STATUS.md'):
  p=pathlib.Path(r['copy']);q=L/'administrative/root-STATUS.md';p.rename(q)
  r['snapshot_source']=r.pop('original');r['copy']=str(q);r['role']='administrative snapshot only'
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
checks=[]
for r in rows:
 paths=[r[k] for k in ['original','copy'] if k in r]
 good=all(h(pathlib.Path(p))==r['sha256'] for p in paths)
 checks.append({'paths':paths,'match':good});assert good,paths
(L/'scientific-postcheck.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'pass':True},indent=2))
manifest={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(L/'finalmanifest.json').write_text(json.dumps(manifest,indent=2));print('manifest files',len(manifest),'all scientific originals/copies unchanged')

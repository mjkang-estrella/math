from retrieve import *
rows=[]
for r in json.loads((L/'freeze.json').read_text())['refs']:
 p=pathlib.Path(r['original']);h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert hashlib.sha256(pathlib.Path(r['copy']).read_bytes()).hexdigest()==r['sha256']
 rows.append({'path':str(p),'sha256':h,'frozen_sha256':r['sha256'],'changed':h!=r['sha256']})
(L/'original-recheck.json').write_text(json.dumps(rows,indent=2))
for r in rows:
 if r['changed']:
  print('CHANGED active original',r['path'],r['frozen_sha256'],r['sha256'])
  print(pathlib.Path(r['path']).read_text()[:1000])
 assert hashlib.sha256(pathlib.Path(r['path']).read_bytes()).hexdigest()==r['sha256']
(L/'failures.jsonl').open('a').write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'first finalize.py','error':'AssertionError: active r226 original changed since initial freeze','resolution':'old frozen copies retained and verified; current original bindings separately recorded; no historical overwrite'})+'\n')

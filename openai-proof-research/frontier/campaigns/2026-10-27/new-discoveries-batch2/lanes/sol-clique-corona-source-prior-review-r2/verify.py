import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def check(p,e):
 b=p.read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],str(p)
m=L/'final-verified-manifest.json';o=json.loads(m.read_bytes())
for e in o['files']:check(L/e['path'],e)
rows=json.loads((L/'before-freeze.json').read_text())['files']+json.loads((L/'after-freeze.json').read_text())['support']
for e in rows:
 check(pathlib.Path(e['path']),e);check(pathlib.Path(e['copy']),e)
for e in map(json.loads,(L/'access.jsonl').read_text().splitlines()):check(L/'retrieved'/e['name'],e)
c=json.loads((L/'checks.json').read_text());assert c['new_2016_body_pages_read']==0 and c['eligibility']=='HOLD'
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':hashlib.sha256(m.read_bytes()).hexdigest(),'payload_files':len(o['files']),'original_and_copy_records':len(rows),'scope':'Integrity/access/coverage assertions only; no source-gap closure or new mathematical proof.'}
(L/'manifest-verification.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

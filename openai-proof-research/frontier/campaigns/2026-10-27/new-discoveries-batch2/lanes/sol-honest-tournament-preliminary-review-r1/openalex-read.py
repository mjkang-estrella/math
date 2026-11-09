import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'path' in r:assert hashlib.sha256(pathlib.Path(r['path']).read_bytes()).hexdigest()==r['sha256']
for x in json.loads((L/'current/openalex').read_text())['results']:
 print(json.dumps({k:x.get(k) for k in ['id','title','doi','publication_date','primary_location','locations','cited_by_count']}))

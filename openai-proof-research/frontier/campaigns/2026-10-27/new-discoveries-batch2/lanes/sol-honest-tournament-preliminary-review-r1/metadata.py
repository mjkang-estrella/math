import pathlib,json,hashlib,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent
for row in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'path' in row:assert hashlib.sha256(pathlib.Path(row['path']).read_bytes()).hexdigest()==row['sha256']
d=json.loads((L/'current/crossref-target').read_text())
for x in d['message']['items']:
 print(json.dumps({k:x.get(k) for k in ['title','DOI','published','link','URL','container-title']}))
print((L/'current/arxiv-prior').read_text())

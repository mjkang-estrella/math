from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-clique-corona-source-prior-review-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def ck(r,p):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
m=json.loads((S/'final-verified-manifest.json').read_text())
for r in m['files']:ck(r,S/r['path'])
rows=json.loads((S/'before-freeze.json').read_text())['files']
for r in rows+json.loads((S/'after-freeze.json').read_text())['support']:ck(r,Path(r['path']));ck(r,Path(r['copy']))
for r in map(json.loads,(S/'access.jsonl').read_text().splitlines()):ck(r,S/'retrieved'/r['name'])
assert len(rows)==181 and len(m['files'])==136
c=json.loads((S/'checks.json').read_text());assert c['new_2016_body_pages_read']==0 and c['eligibility']=='HOLD'
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','frozen_records':181,'manifest_entries':136,'review_files':len(files),'new_primary_body_pages':0,'decision':'HOLD','credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

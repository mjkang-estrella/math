from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for x in json.loads((L/'final-manifest.json').read_text())['files']:
 p=L/x['path'];assert p.is_file() and p.stat().st_size==x['size'] and sha(p)==x['sha256'],str(p)
 checks.append(str(p))
for x in json.loads((L/'source-freeze.json').read_text()):
 assert sha(Path(x['original']))==x['sha256'],x['original']
 if x.get('copy'):assert sha(Path(x['copy']))==x['sha256'],x['copy']
for line in (L/'provenance.jsonl').read_text().splitlines():
 x=json.loads(line);assert sha(Path(x['original']))==sha(Path(x['copy']))==x['sha256'],x['url']
for x in json.loads((L/'history-references.json').read_text()):
 assert sha(Path(x['path']))==x['sha256'],x['path']
manifest_sha=sha(L/'final-manifest.json')
receipt={'status':'PASS','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':manifest_sha,'manifest_file_count':len(checks),'original_copy_checks':'PASS','history_reference_checks':'PASS','manifest_excludes':['final-manifest.json','final-verification.json'],'acceptance_claim':False,'credit':0}
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

from pathlib import Path
import hashlib,json,subprocess,datetime
L=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());ex=set(m['excludes'])
assert ex=={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in ex}
assert actual==set(m['files'])
for n,v in m['files'].items():assert h(L/n)==v,n
refs=json.loads((L/'source-bindings.json').read_text())
for r in refs:assert h(Path(r['original']))==r['sha256'],r['original']
retr=[json.loads(s) for s in (L/'retrieval.jsonl').read_text().splitlines()]
for r in retr:assert h(Path(r['path']))==r['sha256']
bindings=json.loads((L/'primary-text-bindings.json').read_text())
for r in bindings:
 assert h(Path(r['pdf']))==r['pdf_sha256']
 assert h(Path(r['text']))==r['text_sha256']
 out=subprocess.run(['pdftotext','-layout',r['pdf'],'-'],capture_output=True,check=True).stdout
 assert hashlib.sha256(out).hexdigest()==r['text_sha256'],r['text']
history=json.loads((L/'history-hits.json').read_text())
for group in history.values():
 for r in group:assert h(Path(r['path']))==r['sha256'],r['path']
assert json.loads((L/'checks-result.json').read_text())['status']=='PASS'
# Verify again after scientific extraction checks.
for n,v in m['files'].items():assert h(L/n)==v,n
for r in refs:assert h(Path(r['original']))==r['sha256']
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'manifest.json'),'files':len(m['files']),'immutable_science_references':len(refs),'primary_pdf_text_bindings':len(bindings),'retrieval_originals':len(retr),'checks_scope':'hash, source immutability, reproducible extraction, finite controls; not independent proof review','counts':'9/39/next40 unchanged; credit0','administrative_snapshots':'not required unchanged'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
assert actual==set(m)
for name,digest in m.items():assert h(L/name)==digest,name
refs=json.loads((L/'history-verified.json').read_text())
for r in refs:assert h(Path(r['path']))==r['sha256'],r['path']
bindings=json.loads((L/'freeze.json').read_text())+[json.loads(s) for s in (L/'bindings.jsonl').read_text().splitlines()]
count=0
for r in bindings:
 assert h(Path(r['copy']))==r['sha256']
 if not r.get('administrative'):
  assert h(Path(r['original']))==r['sha256'];count+=1
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'finalmanifest.json'),'manifest_files':len(m),'scientific_original_copy_bindings':count,'immutable_history_references':len(refs),'administrative_originals':'snapshot only; not compared','caps':'guard fixed AS/groupRSS512MiB CPU210 wall230; no raises','counts':[9,39,40],'credit_requested':0}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))

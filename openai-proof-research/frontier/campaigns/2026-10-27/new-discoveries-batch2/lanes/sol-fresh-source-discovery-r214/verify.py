from pathlib import Path
import hashlib,json,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for r in json.loads((L/'scientific-bindings.json').read_text()):
 assert h(r['original'])==h(L/r['copy'])==r['sha256'],r
refs=json.loads((L/'reference-bindings.json').read_text())
for r in refs:assert h(r['path'])==r['sha256'],r
for args,name in [([], 'checks.json'),(['--symbolic'],'symbolic.json')]:
 p=subprocess.run([sys.executable,str(L/'checks.py'),*args],capture_output=True,text=True,check=True)
 assert json.loads(p.stdout)==json.loads((L/name).read_text())
m=json.loads((L/'finalmanifest.json').read_text())
assert m['exclusions']==['finalmanifest.json','verification-receipt.json']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
assert actual==set(m['files'])
for name,digest in m['files'].items():assert h(L/name)==digest,name
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 scientific_bindings=len(json.loads((L/'scientific-bindings.json').read_text())),external_snapshot_references=len(refs),
 checker_replays=['finite exact fractions','symbolic rational-function elimination'],manifest_files=len(m['files']),
 manifest_sha256=h(L/'finalmanifest.json'),exclusions=m['exclusions'])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))

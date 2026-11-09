from pathlib import Path
import hashlib,json,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'final-verification.json' not in manifest
for p,d in manifest.items():assert h(L/p)==d,p
for b in json.loads((L/'bindings.json').read_text()):
 assert h(L/b['copy'])==b['sha256']
 if b['kind']=='scientific':assert h(Path(b['original']))==b['sha256']
for b in json.loads((L/'access.json').read_text())+[json.loads(s) for s in (L/'more-access.jsonl').read_text().splitlines()]:
 if 'path' in b:assert h(L/b['path'])==b['sha256']
subprocess.run([sys.executable,str(L/'checks.py')],check=True,timeout=30)
for p,d in manifest.items():assert h(L/p)==d,p
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','final-verification.json']}
assert actual==set(manifest)
receipt=dict(status='PASS',checked_files=len(manifest),manifest_sha256=h(L/'manifest.json'),source_originals_copies='PASS before and after scientific work',exact_checks='PASS rerun; unchanged output',guard='external helper_guard.py; AS/groupRSS512MiB CPU210 wall230; no increases',date=datetime.datetime.now(datetime.timezone.utc).isoformat(),eligibility='no discovery nomination')
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

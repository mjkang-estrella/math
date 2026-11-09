from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text()); checked=0
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert actual==set(m['sha256'])
for name,digest in m['sha256'].items():assert h(L/name)==digest;checked+=1
sources=[json.loads(a) for a in (L/'sources.jsonl').read_text().splitlines()]
for r in sources:assert h(Path(r['original']))==h(Path(r['copy']))==r['sha256']
for r in json.loads((L/'freeze.json').read_text())['references']:
 assert h(Path(r['copy']))==r['sha256']
 if r['kind']=='scientific':assert h(Path(r['original']))==r['sha256']
for r in json.loads((L/'history-references.json').read_text()):assert h(Path(r['path']))==r['sha256']
receipt=dict(status='PASS',time=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'manifest.json'),checked_files=checked,scientific_bindings=len(sources),separate_guarded_invocation=True,scope='integrity only; not proof validation or novelty clearance')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))

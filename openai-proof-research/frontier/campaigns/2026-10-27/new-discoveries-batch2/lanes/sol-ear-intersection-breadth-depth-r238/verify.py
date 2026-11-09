from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());assert 'finalmanifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']};assert actual==set(m)
for p,h in m.items():assert sha(L/p)==h,p
bindings=json.loads((L/'scientificbindings.json').read_text())
for r in bindings:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256'],r
history=json.loads((L/'history-bindings.json').read_text())
for r in history:assert sha(Path(r['path']))==r['sha256'],r['path']
b=json.loads((L/'breadth-checks.json').read_text())['boggle'];w=json.loads((L/'boggle-witness.json').read_text());x=json.loads((L/'mechanisms.json').read_text())
assert len(b['valid_eleven_clues'])==12 and set(w['all_twelve_support_sizes'])=={8} and len(w['embeddings'])==8
assert any(r['n']==6 and r['demand']==2 and r['all_compatible_ear1_targets']==0 for r in x['hall_repair'])
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),files=len(m),scientific_bindings=len(bindings),history_references=len(history),scientific_result='HOLD; no full ear solution or novelty clearance',counts=[9,39,40])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

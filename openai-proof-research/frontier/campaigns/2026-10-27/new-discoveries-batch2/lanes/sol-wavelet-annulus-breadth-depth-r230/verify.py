from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
M=L/'final-manifest.json';m=json.loads(M.read_text());errors=[]
for name,r in m.items():
 p=L/name
 if not p.is_file() or H(p)!=r['sha256'] or p.stat().st_size!=r['size']:errors.append(name)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
assert actual==set(m),('inventory mismatch',actual^set(m))
for r in json.loads((L/'freeze.json').read_text()):
 for key in ['original','copy']:
  if H(Path(r[key]))!=r['sha256']:errors.append(key+':'+r[key])
history_drift=[]
for r in json.loads((L/'history-references.json').read_text()):
 p=Path(r['path'])
 if not p.is_file() or H(p)!=r['sha256']:history_drift.append(str(p))
for line in (L/'retrieval.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'path' in r and H(Path(r['path']))!=r['sha256']:errors.append(r['path'])
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not errors,'manifest_sha256':H(M),'files':len(m),'errors':errors,'history_drift':history_drift,'manifest_excludes_self_and_receipt':True,'scientific_status':'unresolved; no novelty clearance; no credit','method':'separate guarded verification after all writes; administrative originals are not asserted immutable'}
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out));assert not errors

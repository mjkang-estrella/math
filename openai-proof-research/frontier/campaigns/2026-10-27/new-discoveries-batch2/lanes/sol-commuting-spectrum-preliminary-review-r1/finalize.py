from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'bindings.json').read_text())
for r in rows:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256'],r
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):assert sha(Path(r['path']))==r['sha256']
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'provenance.json').write_text(json.dumps(dict(role='solo independent review',recommendation='EXCLUDE: substantive routine bridge; mathematics PASS',counts=dict(additional=9,total=39,next=40),source_binding_count=len(rows),postread_original_copy_check='PASS',guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024**2,sampled_group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230),administrative_policy='snapshots only',retrievals='access.jsonl: saved/hash-bound before body read',utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
exclude={'final-manifest.json','verification-receipt.json','finalize.log','verify.log'}
files={str(p.relative_to(L)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclude}
(L/'final-manifest.json').write_text(json.dumps(dict(excludes=sorted(exclude),files=files),indent=2)+'\n')
print(json.dumps(dict(status='PASS',bound_inputs=len(rows),manifest_files=len(files),manifest_sha256=sha(L/'final-manifest.json'))))

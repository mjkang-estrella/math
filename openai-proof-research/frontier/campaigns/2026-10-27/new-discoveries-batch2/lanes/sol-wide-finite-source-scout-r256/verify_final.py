from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
issues=[];manifest=json.loads((L/'final-manifest.json').read_text())
for n,h in manifest.items():
 p=L/n
 if not p.is_file() or sha(p)!=h:issues.append({'manifest_mismatch':n})
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']}
if actual!=set(manifest):issues.append({'inventory_difference':sorted(actual^set(manifest))})
for r in json.loads((L/'bindings.json').read_text()):
 if sha(Path(r['copy']))!=r['sha256']:issues.append({'copy_changed':r['copy']})
 if not r['administrative'] and sha(Path(r['original']))!=r['sha256']:issues.append({'scientific_original_changed':r['original']})
for r in json.loads((L/'history-bindings.json').read_text()):
 if sha(Path(r['path']))!=r['sha256']:issues.append({'historical_original_changed':r['path']})
for r in json.loads((L/'sources/bindings.json').read_text()):
 if 'sha256' in r and sha(Path(r['path']))!=r['sha256']:issues.append({'retrieved_source_changed':r['path']})
out=dict(status='PASS' if not issues else 'FAIL',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'final-manifest.json'),artifact_count=len(manifest),issues=issues,administrative_policy='snapshots verified; mutable administrative originals not compared',exclusions=['final-manifest.json','final-verification.json'],scope='separate post-write byte verification, not theorem/novelty acceptance')
(L/'final-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
raise SystemExit(bool(issues))

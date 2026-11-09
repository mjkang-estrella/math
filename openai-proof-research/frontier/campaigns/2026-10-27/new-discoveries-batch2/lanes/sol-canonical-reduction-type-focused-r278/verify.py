from pathlib import Path
import json,hashlib,datetime,subprocess,sys,resource
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=[];manifest=json.loads((L/'MANIFEST.json').read_text())
for r in manifest['files']:
 p=L/r['path']
 if not p.is_file() or sha(p)!=r['sha256']:fail.append('manifest '+r['path'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
if actual!={r['path'] for r in manifest['files']}:fail.append('file inventory')
refs=json.loads((L/'source-bindings.json').read_text())
for r in refs:
 if sha(Path(r['path']))!=r['sha256']:fail.append('source '+r['path'])
for r in json.loads((L/'admin-bindings.json').read_text()):
 if sha(L/r['copy'])!=r['sha256']:fail.append('admin snapshot '+r['copy'])
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'sha256' in r:
  p=L/r['path']
  if sha(p)!=r['sha256']:fail.append('download '+r['path'])
  if 'text_sha256' in r and sha(p.with_suffix('.txt'))!=r['text_sha256']:fail.append('extraction '+r['path'])
before=sha(L/'exact-checks.json')
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True)
if p.returncode or before!=sha(L/'exact-checks.json'):fail.append('exact reproducibility')
if (L/'PROOF.md').exists():fail.append('unexpected PROOF.md')
prov=json.loads((L/'provenance.json').read_text())
if sha(Path(prov['guard']['path']))!=prov['guard']['sha256']:fail.append('guard identity')
receipt=dict(status='PASS' if not fail else 'FAIL',at=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'MANIFEST.json'),files_checked=len(manifest['files']),references_checked=len(refs),exact_check_rerun_exit=p.returncode,exact_check_same_hash=before==sha(L/'exact-checks.json'),limits=dict(AS=resource.getrlimit(resource.RLIMIT_AS),CPU=resource.getrlimit(resource.RLIMIT_CPU),group_RSS_and_wall='outer unchanged helper_guard'),failures=fail,meaning='artifact/source integrity and exact diagnostic replay only; no theorem or novelty acceptance')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
sys.exit(bool(fail))

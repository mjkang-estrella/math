from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=0
def check(p,h):
 global checks
 assert sha(p)==h, str(p)
 checks+=1
for n in ['freeze.json','registry-freeze.json']:
 for r in json.loads((L/n).read_text())['files']:check(Path(r['path']),r['sha256'])
for r in json.loads((L/'registry-head-bindings.json').read_text()):check(Path(r['path']),r['sha256'])
for name in ['sol-quantile-aggregation-full-r1','sol-quantile-aggregation-preliminary-review-r1']:
 D=L.parent/name
 for p,h in json.loads((D/'manifest.json').read_text()).items():check(D/p,h)
 for r in json.loads((D/'freeze.json').read_text()):
  check(Path(r['original']),r['sha256']);check(D/r['copy'],r['sha256'])
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):
 if 'sha256' in r:check(L/(r['name']+'.body'),r['sha256'])
for r in map(json.loads,(L/'derived.jsonl').read_text().splitlines()):check(L/r['file'],r['sha256'])
for n in ['ledger.json','prior-campaign-context.json']:json.loads((L/'administrative'/n).read_text())
if '--final' in sys.argv:
 m=json.loads((L/'manifest.json').read_text())
 assert set(m)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 for p,h in m.items():check(L/p,h)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','hash_checks':checks,'stage':'final' if '--final' in sys.argv else 'pre-final','resource_limits':'AS/groupRSS512MiB CPU210 wall230; assigned helper_guard','scope':'reference bindings, inherited original/copy maps and manifests, response and derived hashes; no mathematical replay'}
(L/('verification-receipt.json' if '--final' in sys.argv else 'integrity-before-report.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))

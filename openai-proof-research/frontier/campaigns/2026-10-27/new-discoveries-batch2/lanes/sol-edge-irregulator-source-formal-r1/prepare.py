import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210))
import json,hashlib,shutil,datetime
from pathlib import Path
R=Path(__file__).resolve().parent;B=R.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'root-edge-irregulator-review-freeze-r1/review-freeze.json';d=json.loads(f.read_text())
rows=[]
for n,h in d['files'].items():
 p=Path(d['source_lane'])/n;assert sha(p)==h,n
 q=R/'inputs/candidate'/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert sha(q)==h
 rows.append({'path':n,'sha256':h})
assert len(rows)==79
assert set(d['files'])=={str(p.relative_to(Path(d['source_lane']))) for p in Path(d['source_lane']).rglob('*') if p.is_file()}
(R/'freeze-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows,'freeze_sha256':sha(f)},indent=2))
for p in [f,B/'root-edge-irregulator-formal-investment-r1/ADOPTION.json',B/'sol-edge-irregulator-preliminary-review-r1/review.md',B/'sol-edge-irregulator-current-prior-review-r2/review.md',B/'sol-edge-irregulator-current-prior-review-r2/live/publisher.pdf',B.parent/'ledger.json',B.parent/'prior-campaign-context.json']:
 q=R/'inputs'/p.parent.name/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
assert sha(R/'inputs/live/publisher.pdf')=='574aaf95e9d6e94273d2ebc15704bb1209537625d7e59b5282d9a130efb1ceae'
pins=json.loads((R/'pins.json').read_text());assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
for p in pins['packages']:
 g=Path(p['path'])/'.git';h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:];x=g/ref;h=x.read_text().strip() if x.exists() else next(l.split()[0] for l in (g/'packed-refs').read_text().splitlines() if l.endswith(' '+ref))
 assert h==p['rev'],p['name']
print('79 frozen files, publisher PDF, Lean binary, all 9 package pins verified (mathlib + 8).')
